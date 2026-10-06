/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C090C001Part025Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part025`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0001`. -/
@[expose]
noncomputable def nb090SplitAlpha0001 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy063 A), (nb090AlphaDummy064 h)),
        ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy063 A))
          (Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCphi (Class.cv (nb090AlphaDummy058 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy063 A))
            (Class.cab (nb090AlphaDummy057 A)
              (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                  (synCphi (Class.cv (nb090AlphaDummy058 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy064 h))
          (Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCphi (Class.cv (nb090AlphaDummy060 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy064 h))
            (Class.cab (nb090AlphaDummy059 h)
              (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                  (synCphi (Class.cv (nb090AlphaDummy060 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy058 A) from (by
                      unfold nb090AlphaDummy058;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 1))))
                  (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy060 h) from (by
                      unfold nb090AlphaDummy060;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy057 A) from (by
                        unfold nb090AlphaDummy057;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0046 A) 0))))
                    (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy059 h) from (by
                        unfold nb090AlphaDummy059;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0048 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy063 A) from (by
                          unfold nb090AlphaDummy063;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0050 A) 0))))
                      (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy064 h) from (by
                          unfold nb090AlphaDummy064;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0051 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy061 A) from (by
                            unfold nb090AlphaDummy061;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0047 A) 0))))
                        (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy062 h) from (by
                            unfold nb090AlphaDummy062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0049 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb090AlphaDummy000 A))).fv ∪
                              ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) (by decide))
                          (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy049 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy050 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy065 A) from (by
                              unfold nb090AlphaDummy065;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0052 A) 0))))
                          (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy067 h) from (by
                              unfold nb090AlphaDummy067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0053 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy066 A) from (by
                                unfold nb090AlphaDummy066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0052 A) 1))))
                            (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy068 h) from (by
                                unfold nb090AlphaDummy068;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0053 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy058 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy060 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy072 A) from (by
          unfold nb090AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 1)))) (show (nb090AlphaDummy067 h) ≠
        (nb090AlphaDummy075 h) from (by
          unfold nb090AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy071 A) from (by
          unfold nb090AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 0)))) (show (nb090AlphaDummy067 h) ≠
        (nb090AlphaDummy074 h) from (by
          unfold nb090AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from (by
          unfold nb090AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0054 A)
                  0)))) (show (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h) from (by
          unfold nb090AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0055 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy073 A), (nb090AlphaDummy076 h)), ((nb090AlphaDummy072 A),
        (nb090AlphaDummy075 h)), ((nb090AlphaDummy071 A), (nb090AlphaDummy074 h)),
        ((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)), ((nb090AlphaDummy065 A),
        (nb090AlphaDummy067 h)), ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
        ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)), ((nb090AlphaDummy057 A),
        (nb090AlphaDummy059 h)), ((nb090AlphaDummy063 A), (nb090AlphaDummy064 h)),
        ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)), ((nb090AlphaDummy050 A),
        (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A),
        (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy072
        A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy073 A), (nb090AlphaDummy076 h)), ((nb090AlphaDummy072 A),
        (nb090AlphaDummy075 h)), ((nb090AlphaDummy071 A), (nb090AlphaDummy074 h)),
        ((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)), ((nb090AlphaDummy065 A),
        (nb090AlphaDummy067 h)), ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
        ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)), ((nb090AlphaDummy057 A),
        (nb090AlphaDummy059 h)), ((nb090AlphaDummy063 A), (nb090AlphaDummy064 h)),
        ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)), ((nb090AlphaDummy050 A),
        (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A),
        (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy067
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy083 A) from (by
          unfold
            nb090AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy084 h) from (by
          unfold
            nb090AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy083 A) from (by
          unfold
            nb090AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy084 h) from (by
          unfold
            nb090AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy073
        A) ≠ (nb090AlphaDummy085 A) from (by
          unfold
            nb090AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy086 h) from (by
          unfold
            nb090AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy073
        A) ≠ (nb090AlphaDummy085 A) from (by
          unfold
            nb090AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy086 h) from (by
          unfold
            nb090AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from
                                      (by
                                        unfold nb090AlphaDummy069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0054 A)
                                                0)))) (show (nb090AlphaDummy067 h) ≠
                                        (nb090AlphaDummy070 h) from (by
                                        unfold nb090AlphaDummy070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0055 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)),
                                    ((nb090AlphaDummy065 A), (nb090AlphaDummy067 h)),
                                    ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
                                    ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
                                    ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)),
                                    ((nb090AlphaDummy063 A), (nb090AlphaDummy064 h)),
                                    ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from
                                    (by
                                      unfold nb090AlphaDummy069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h) from
                                    (by
                                      unfold nb090AlphaDummy070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from
                                      (by
                                        unfold nb090AlphaDummy069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0054 A)
                                                0)))) (show (nb090AlphaDummy067 h) ≠
                                        (nb090AlphaDummy070 h) from (by
                                        unfold nb090AlphaDummy070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0055 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)),
                                    ((nb090AlphaDummy065 A), (nb090AlphaDummy067 h)),
                                    ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
                                    ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
                                    ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)),
                                    ((nb090AlphaDummy063 A), (nb090AlphaDummy064 h)),
                                    ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy058 A) from (by
                        unfold nb090AlphaDummy058;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0046 A) 1))))
                    (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy060 h) from (by
                        unfold nb090AlphaDummy060;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0048 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy057 A) from (by
                          unfold nb090AlphaDummy057;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0046 A) 0))))
                      (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy059 h) from (by
                          unfold nb090AlphaDummy059;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0048 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy063 A) from (by
                            unfold nb090AlphaDummy063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0050 A) 0))))
                        (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy064 h) from (by
                            unfold nb090AlphaDummy064;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0051 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy061 A) from (by
                              unfold nb090AlphaDummy061;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0047 A) 0))))
                          (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy062 h) from (by
                              unfold nb090AlphaDummy062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0049 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy000 A))).fv ∪
                                ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy049 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy050 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy053 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy065 A) from (by
                                unfold nb090AlphaDummy065;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0052 A) 0))))
                            (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy067 h) from (by
                                unfold nb090AlphaDummy067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0053 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy066 A) from
                                (by
                                  unfold nb090AlphaDummy066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0052 A) 1))))
                              (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy068 h) from
                                (by
                                  unfold nb090AlphaDummy068;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0053 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy058 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy060 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy072 A) from (by
          unfold nb090AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 1)))) (show (nb090AlphaDummy067 h) ≠
        (nb090AlphaDummy075 h) from (by
          unfold nb090AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy071 A) from (by
          unfold nb090AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A)
                  0)))) (show (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy074 h) from (by
          unfold nb090AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy065 A) ≠
        (nb090AlphaDummy069 A) from (by
          unfold nb090AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0054 A)
                  0)))) (show (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h) from (by
          unfold nb090AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0055 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy073 A), (nb090AlphaDummy076 h)), ((nb090AlphaDummy072 A),
        (nb090AlphaDummy075 h)), ((nb090AlphaDummy071 A), (nb090AlphaDummy074 h)),
        ((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)), ((nb090AlphaDummy065 A),
        (nb090AlphaDummy067 h)), ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
        ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)), ((nb090AlphaDummy057 A),
        (nb090AlphaDummy059 h)), ((nb090AlphaDummy063 A), (nb090AlphaDummy064 h)),
        ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)), ((nb090AlphaDummy050 A),
        (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A),
        (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy072
        A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy073 A), (nb090AlphaDummy076 h)), ((nb090AlphaDummy072 A),
        (nb090AlphaDummy075 h)), ((nb090AlphaDummy071 A), (nb090AlphaDummy074 h)),
        ((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)), ((nb090AlphaDummy065 A),
        (nb090AlphaDummy067 h)), ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
        ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)), ((nb090AlphaDummy057 A),
        (nb090AlphaDummy059 h)), ((nb090AlphaDummy063 A), (nb090AlphaDummy064 h)),
        ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)), ((nb090AlphaDummy050 A),
        (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A),
        (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy067
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy083 A) from (by
          unfold
            nb090AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy084 h) from (by
          unfold
            nb090AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy083 A) from (by
          unfold
            nb090AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy084 h) from (by
          unfold
            nb090AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy073
        A) ≠ (nb090AlphaDummy085 A) from (by
          unfold
            nb090AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy086 h) from (by
          unfold
            nb090AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy073
        A) ≠ (nb090AlphaDummy085 A) from (by
          unfold
            nb090AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy086 h) from (by
          unfold
            nb090AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A)
                                        from (by
                                          unfold nb090AlphaDummy069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0054 A) 0)))) (show
                                        (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h)
                                        from (by
                                          unfold nb090AlphaDummy070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0055 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)),
                                      ((nb090AlphaDummy065 A), (nb090AlphaDummy067 h)),
                                      ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
                                      ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
                                      ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)),
                                      ((nb090AlphaDummy063 A), (nb090AlphaDummy064 h)),
                                      ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
                                      ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                      ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                      ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                      ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                      ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from
                                      (by
                                        unfold nb090AlphaDummy069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0054 A)
                                                0)))) (show (nb090AlphaDummy067 h) ≠
                                        (nb090AlphaDummy070 h) from (by
                                        unfold nb090AlphaDummy070;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0055 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A)
                                        from (by
                                          unfold nb090AlphaDummy069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0054 A) 0)))) (show
                                        (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h)
                                        from (by
                                          unfold nb090AlphaDummy070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0055 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)),
                                      ((nb090AlphaDummy065 A), (nb090AlphaDummy067 h)),
                                      ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
                                      ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
                                      ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)),
                                      ((nb090AlphaDummy063 A), (nb090AlphaDummy064 h)),
                                      ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
                                      ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                      ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                      ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                      ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                      ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part026`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0002`. -/
@[expose]
noncomputable def nb090SplitAlpha0002 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy089 A), (nb090AlphaDummy090 h)),
        ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
        ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)),
        ((nb090AlphaDummy087 A), (nb090AlphaDummy088 h)),
        ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.classMem (Class.cv (nb090AlphaDummy089 A))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy058 A)))))
      (Wff.classMem (Class.cv (nb090AlphaDummy090 h))
        (synCcompl (synCphi (Class.cv (nb090AlphaDummy060 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy065 A) from (by
                            unfold nb090AlphaDummy065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0052 A) 0))))
                        (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy067 h) from (by
                            unfold nb090AlphaDummy067;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0053 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy066 A) from (by
                              unfold nb090AlphaDummy066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0052 A) 1))))
                          (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy068 h) from (by
                              unfold nb090AlphaDummy068;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0053 h) 1))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy091 A) from (by
                                unfold nb090AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0082 A) 0))))
                            (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy092 h) from (by
                                unfold nb090AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0083 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy089 A) from
                                (by
                                  unfold nb090AlphaDummy089;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0080 A) 0))))
                              (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy090 h) from
                                (by
                                  unfold nb090AlphaDummy090;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0081 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy058 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy060 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy065 A) ≠
        (nb090AlphaDummy072 A) from (by
          unfold nb090AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 1)))) (show (nb090AlphaDummy067 h) ≠
        (nb090AlphaDummy075 h) from (by
          unfold nb090AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy071 A) from (by
          unfold nb090AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 0)))) (show (nb090AlphaDummy067 h) ≠
        (nb090AlphaDummy074 h) from (by
          unfold nb090AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from (by
          unfold nb090AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0054 A) 0)))) (show (nb090AlphaDummy067 h) ≠
        (nb090AlphaDummy070 h) from (by
          unfold nb090AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0055 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy073 A), (nb090AlphaDummy076 h)), ((nb090AlphaDummy072 A),
        (nb090AlphaDummy075 h)), ((nb090AlphaDummy071 A), (nb090AlphaDummy074 h)),
        ((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)), ((nb090AlphaDummy065 A),
        (nb090AlphaDummy067 h)), ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
        ((nb090AlphaDummy091 A), (nb090AlphaDummy092 h)), ((nb090AlphaDummy089 A),
        (nb090AlphaDummy090 h)), ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
        ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)), ((nb090AlphaDummy087 A),
        (nb090AlphaDummy088 h)), ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy073 A), (nb090AlphaDummy076 h)), ((nb090AlphaDummy072 A),
        (nb090AlphaDummy075 h)), ((nb090AlphaDummy071 A), (nb090AlphaDummy074 h)),
        ((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)), ((nb090AlphaDummy065 A),
        (nb090AlphaDummy067 h)), ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
        ((nb090AlphaDummy091 A), (nb090AlphaDummy092 h)), ((nb090AlphaDummy089 A),
        (nb090AlphaDummy090 h)), ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
        ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)), ((nb090AlphaDummy087 A),
        (nb090AlphaDummy088 h)), ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy067 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy072
        A) ≠ (nb090AlphaDummy083 A) from (by
          unfold
            nb090AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy084 h) from (by
          unfold
            nb090AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy083 A) from (by
          unfold
            nb090AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy084 h) from (by
          unfold
            nb090AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy073
        A) ≠ (nb090AlphaDummy085 A) from (by
          unfold
            nb090AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy086 h) from (by
          unfold
            nb090AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy073
        A) ≠ (nb090AlphaDummy085 A) from (by
          unfold
            nb090AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy086 h) from (by
          unfold
            nb090AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from
                                    (by
                                      unfold nb090AlphaDummy069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h) from
                                    (by
                                      unfold nb090AlphaDummy070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)),
                                  ((nb090AlphaDummy065 A), (nb090AlphaDummy067 h)),
                                  ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
                                  ((nb090AlphaDummy091 A), (nb090AlphaDummy092 h)),
                                  ((nb090AlphaDummy089 A), (nb090AlphaDummy090 h)),
                                  ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
                                  ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)),
                                  ((nb090AlphaDummy087 A), (nb090AlphaDummy088 h)),
                                  ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
                                  ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                  ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                  ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                  ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                  ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from (by
                                    unfold nb090AlphaDummy069;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0054 A)
                                            0)))) (show
                                  (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h) from (by
                                    unfold nb090AlphaDummy070;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0055 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from
                                    (by
                                      unfold nb090AlphaDummy069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h) from
                                    (by
                                      unfold nb090AlphaDummy070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)),
                                  ((nb090AlphaDummy065 A), (nb090AlphaDummy067 h)),
                                  ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
                                  ((nb090AlphaDummy091 A), (nb090AlphaDummy092 h)),
                                  ((nb090AlphaDummy089 A), (nb090AlphaDummy090 h)),
                                  ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
                                  ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)),
                                  ((nb090AlphaDummy087 A), (nb090AlphaDummy088 h)),
                                  ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
                                  ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                  ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                  ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                  ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                  ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy065 A) from (by
                            unfold nb090AlphaDummy065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0052 A) 0))))
                        (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy067 h) from (by
                            unfold nb090AlphaDummy067;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0053 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy066 A) from (by
                              unfold nb090AlphaDummy066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0052 A) 1))))
                          (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy068 h) from (by
                              unfold nb090AlphaDummy068;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0053 h) 1))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy091 A) from (by
                                unfold nb090AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0082 A) 0))))
                            (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy092 h) from (by
                                unfold nb090AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0083 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy058 A) ≠ (nb090AlphaDummy089 A) from
                                (by
                                  unfold nb090AlphaDummy089;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0080 A) 0))))
                              (show (nb090AlphaDummy060 h) ≠ (nb090AlphaDummy090 h) from
                                (by
                                  unfold nb090AlphaDummy090;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0081 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090AlphaDummy058 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090AlphaDummy060 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy065 A) ≠
        (nb090AlphaDummy072 A) from (by
          unfold nb090AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 1)))) (show (nb090AlphaDummy067 h) ≠
        (nb090AlphaDummy075 h) from (by
          unfold nb090AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy071 A) from (by
          unfold nb090AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0056 A) 0)))) (show (nb090AlphaDummy067 h) ≠
        (nb090AlphaDummy074 h) from (by
          unfold nb090AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0057 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from (by
          unfold nb090AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0054 A) 0)))) (show (nb090AlphaDummy067 h) ≠
        (nb090AlphaDummy070 h) from (by
          unfold nb090AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0055 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy073 A), (nb090AlphaDummy076 h)), ((nb090AlphaDummy072 A),
        (nb090AlphaDummy075 h)), ((nb090AlphaDummy071 A), (nb090AlphaDummy074 h)),
        ((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)), ((nb090AlphaDummy065 A),
        (nb090AlphaDummy067 h)), ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
        ((nb090AlphaDummy091 A), (nb090AlphaDummy092 h)), ((nb090AlphaDummy089 A),
        (nb090AlphaDummy090 h)), ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
        ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)), ((nb090AlphaDummy087 A),
        (nb090AlphaDummy088 h)), ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0060
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0061
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0058
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0059
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠ (nb090AlphaDummy079 A) from (by
          unfold
            nb090AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0064
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy080 h) from (by
          unfold
            nb090AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0065
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy077 A) from (by
          unfold
            nb090AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0062
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy078 h) from (by
          unfold
            nb090AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0063
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy073 A), (nb090AlphaDummy076 h)), ((nb090AlphaDummy072 A),
        (nb090AlphaDummy075 h)), ((nb090AlphaDummy071 A), (nb090AlphaDummy074 h)),
        ((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)), ((nb090AlphaDummy065 A),
        (nb090AlphaDummy067 h)), ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
        ((nb090AlphaDummy091 A), (nb090AlphaDummy092 h)), ((nb090AlphaDummy089 A),
        (nb090AlphaDummy090 h)), ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
        ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)), ((nb090AlphaDummy087 A),
        (nb090AlphaDummy088 h)), ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy067 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy072
        A) ≠ (nb090AlphaDummy083 A) from (by
          unfold
            nb090AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy084 h) from (by
          unfold
            nb090AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy083 A) from (by
          unfold
            nb090AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0068
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy084 h) from (by
          unfold
            nb090AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0069
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy072 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0066
                    A)
                  0)))) (show (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0067
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy065
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy073
        A) ≠ (nb090AlphaDummy085 A) from (by
          unfold
            nb090AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy086 h) from (by
          unfold
            nb090AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy073
        A) ≠ (nb090AlphaDummy085 A) from (by
          unfold
            nb090AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0072
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy086 h) from (by
          unfold
            nb090AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0073
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy073 A) ≠
        (nb090AlphaDummy081 A) from (by
          unfold
            nb090AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0070
                    A)
                  0)))) (show (nb090AlphaDummy076 h) ≠ (nb090AlphaDummy082 h) from (by
          unfold
            nb090AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0071
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from
                                    (by
                                      unfold nb090AlphaDummy069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h) from
                                    (by
                                      unfold nb090AlphaDummy070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)),
                                  ((nb090AlphaDummy065 A), (nb090AlphaDummy067 h)),
                                  ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
                                  ((nb090AlphaDummy091 A), (nb090AlphaDummy092 h)),
                                  ((nb090AlphaDummy089 A), (nb090AlphaDummy090 h)),
                                  ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
                                  ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)),
                                  ((nb090AlphaDummy087 A), (nb090AlphaDummy088 h)),
                                  ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
                                  ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                  ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                  ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                  ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                  ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from (by
                                    unfold nb090AlphaDummy069;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0054 A)
                                            0)))) (show
                                  (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h) from (by
                                    unfold nb090AlphaDummy070;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0055 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy069 A) from
                                    (by
                                      unfold nb090AlphaDummy069;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0054 A)
                                              0)))) (show
                                    (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy070 h) from
                                    (by
                                      unfold nb090AlphaDummy070;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0055 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
                                [((nb090AlphaDummy069 A), (nb090AlphaDummy070 h)),
                                  ((nb090AlphaDummy065 A), (nb090AlphaDummy067 h)),
                                  ((nb090AlphaDummy066 A), (nb090AlphaDummy068 h)),
                                  ((nb090AlphaDummy091 A), (nb090AlphaDummy092 h)),
                                  ((nb090AlphaDummy089 A), (nb090AlphaDummy090 h)),
                                  ((nb090AlphaDummy058 A), (nb090AlphaDummy060 h)),
                                  ((nb090AlphaDummy057 A), (nb090AlphaDummy059 h)),
                                  ((nb090AlphaDummy087 A), (nb090AlphaDummy088 h)),
                                  ((nb090AlphaDummy061 A), (nb090AlphaDummy062 h)),
                                  ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                  ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                  ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                  ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                  ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                  ((nb090AlphaDummy000 A), h),
                                  ((nb090AlphaDummy002 A), v),
                                  ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                    (nb090AlphaDummy004 v u A h))]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part027`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0003`. -/
@[expose]
noncomputable def nb090SplitAlpha0003 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy099 A), (nb090AlphaDummy100 h)),
        ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy099 A))
          (Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCphi (Class.cv (nb090AlphaDummy094 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy099 A))
            (Class.cab (nb090AlphaDummy093 A)
              (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                  (synCphi (Class.cv (nb090AlphaDummy094 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy100 h))
          (Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCphi (Class.cv (nb090AlphaDummy096 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy100 h))
            (Class.cab (nb090AlphaDummy095 h)
              (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                  (synCphi (Class.cv (nb090AlphaDummy096 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy094 A) from (by
                      unfold nb090AlphaDummy094;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 1))))
                  (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy096 h) from (by
                      unfold nb090AlphaDummy096;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy093 A) from (by
                        unfold nb090AlphaDummy093;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0084 A) 0))))
                    (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy095 h) from (by
                        unfold nb090AlphaDummy095;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0086 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy099 A) from (by
                          unfold nb090AlphaDummy099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0088 A) 0))))
                      (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy100 h) from (by
                          unfold nb090AlphaDummy100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0089 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy097 A) from (by
                            unfold nb090AlphaDummy097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0085 A) 0))))
                        (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy098 h) from (by
                            unfold nb090AlphaDummy098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0087 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb090AlphaDummy000 A))).fv ∪
                              ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) (by decide))
                          (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy000 A))).fv ∪
                                ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy049 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy051 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy054 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy101 A) from (by
                              unfold nb090AlphaDummy101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0090 A) 0))))
                          (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy103 h) from (by
                              unfold nb090AlphaDummy103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0091 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy102 A) from (by
                                unfold nb090AlphaDummy102;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0090 A) 1))))
                            (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy104 h) from (by
                                unfold nb090AlphaDummy104;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0091 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy094 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy096 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy108 A) from (by
          unfold nb090AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A) 1)))) (show (nb090AlphaDummy103 h) ≠
        (nb090AlphaDummy111 h) from (by
          unfold nb090AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy107 A) from (by
          unfold nb090AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A) 0)))) (show (nb090AlphaDummy103 h) ≠
        (nb090AlphaDummy110 h) from (by
          unfold nb090AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from (by
          unfold nb090AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0092 A)
                  0)))) (show (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h) from (by
          unfold nb090AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0093 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy109 A), (nb090AlphaDummy112 h)), ((nb090AlphaDummy108 A),
        (nb090AlphaDummy111 h)), ((nb090AlphaDummy107 A), (nb090AlphaDummy110 h)),
        ((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)), ((nb090AlphaDummy101 A),
        (nb090AlphaDummy103 h)), ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
        ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)), ((nb090AlphaDummy093 A),
        (nb090AlphaDummy095 h)), ((nb090AlphaDummy099 A), (nb090AlphaDummy100 h)),
        ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy109 A), (nb090AlphaDummy112 h)), ((nb090AlphaDummy108 A),
        (nb090AlphaDummy111 h)), ((nb090AlphaDummy107 A), (nb090AlphaDummy110 h)),
        ((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)), ((nb090AlphaDummy101 A),
        (nb090AlphaDummy103 h)), ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
        ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)), ((nb090AlphaDummy093 A),
        (nb090AlphaDummy095 h)), ((nb090AlphaDummy099 A), (nb090AlphaDummy100 h)),
        ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy103 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy108
        A) ≠ (nb090AlphaDummy119 A) from (by
          unfold
            nb090AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy120 h) from (by
          unfold
            nb090AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy119 A) from (by
          unfold
            nb090AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy120 h) from (by
          unfold
            nb090AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy109
        A) ≠ (nb090AlphaDummy121 A) from (by
          unfold
            nb090AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy122 h) from (by
          unfold
            nb090AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy109
        A) ≠ (nb090AlphaDummy121 A) from (by
          unfold
            nb090AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy122 h) from (by
          unfold
            nb090AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from
                                      (by
                                        unfold nb090AlphaDummy105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0092 A)
                                                0)))) (show (nb090AlphaDummy103 h) ≠
                                        (nb090AlphaDummy106 h) from (by
                                        unfold nb090AlphaDummy106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0093 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
                                    ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
                                    ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
                                    ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
                                    ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
                                    ((nb090AlphaDummy099 A), (nb090AlphaDummy100 h)),
                                    ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
                                    ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from
                                    (by
                                      unfold nb090AlphaDummy105;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0092 A)
                                              0)))) (show
                                    (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h) from
                                    (by
                                      unfold nb090AlphaDummy106;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0093 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from
                                      (by
                                        unfold nb090AlphaDummy105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0092 A)
                                                0)))) (show (nb090AlphaDummy103 h) ≠
                                        (nb090AlphaDummy106 h) from (by
                                        unfold nb090AlphaDummy106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0093 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
                                    ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
                                    ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
                                    ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
                                    ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
                                    ((nb090AlphaDummy099 A), (nb090AlphaDummy100 h)),
                                    ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
                                    ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy094 A) from (by
                        unfold nb090AlphaDummy094;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0084 A) 1))))
                    (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy096 h) from (by
                        unfold nb090AlphaDummy096;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0086 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy093 A) from (by
                          unfold nb090AlphaDummy093;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0084 A) 0))))
                      (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy095 h) from (by
                          unfold nb090AlphaDummy095;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0086 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy099 A) from (by
                            unfold nb090AlphaDummy099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0088 A) 0))))
                        (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy100 h) from (by
                            unfold nb090AlphaDummy100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0089 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy097 A) from (by
                              unfold nb090AlphaDummy097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0085 A) 0))))
                          (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy098 h) from (by
                              unfold nb090AlphaDummy098;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0087 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy000 A))).fv ∪
                                ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb090AlphaDummy000 A))).fv ∪
                                  ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy049 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy051 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy054 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy101 A) from (by
                                unfold nb090AlphaDummy101;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0090 A) 0))))
                            (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy103 h) from (by
                                unfold nb090AlphaDummy103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0091 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy102 A) from
                                (by
                                  unfold nb090AlphaDummy102;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0090 A) 1))))
                              (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy104 h) from
                                (by
                                  unfold nb090AlphaDummy104;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0091 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy094 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy096 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy108 A) from (by
          unfold nb090AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A) 1)))) (show (nb090AlphaDummy103 h) ≠
        (nb090AlphaDummy111 h) from (by
          unfold nb090AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy107 A) from (by
          unfold nb090AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A)
                  0)))) (show (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy110 h) from (by
          unfold nb090AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy101 A) ≠
        (nb090AlphaDummy105 A) from (by
          unfold nb090AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0092 A)
                  0)))) (show (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h) from (by
          unfold nb090AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0093 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy109 A), (nb090AlphaDummy112 h)), ((nb090AlphaDummy108 A),
        (nb090AlphaDummy111 h)), ((nb090AlphaDummy107 A), (nb090AlphaDummy110 h)),
        ((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)), ((nb090AlphaDummy101 A),
        (nb090AlphaDummy103 h)), ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
        ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)), ((nb090AlphaDummy093 A),
        (nb090AlphaDummy095 h)), ((nb090AlphaDummy099 A), (nb090AlphaDummy100 h)),
        ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy109 A), (nb090AlphaDummy112 h)), ((nb090AlphaDummy108 A),
        (nb090AlphaDummy111 h)), ((nb090AlphaDummy107 A), (nb090AlphaDummy110 h)),
        ((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)), ((nb090AlphaDummy101 A),
        (nb090AlphaDummy103 h)), ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
        ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)), ((nb090AlphaDummy093 A),
        (nb090AlphaDummy095 h)), ((nb090AlphaDummy099 A), (nb090AlphaDummy100 h)),
        ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy103
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy108
        A) ≠ (nb090AlphaDummy119 A) from (by
          unfold
            nb090AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy120 h) from (by
          unfold
            nb090AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy119 A) from (by
          unfold
            nb090AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy120 h) from (by
          unfold
            nb090AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy109
        A) ≠ (nb090AlphaDummy121 A) from (by
          unfold
            nb090AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy122 h) from (by
          unfold
            nb090AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy109
        A) ≠ (nb090AlphaDummy121 A) from (by
          unfold
            nb090AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy122 h) from (by
          unfold
            nb090AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A)
                                        from (by
                                          unfold nb090AlphaDummy105;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0092 A) 0)))) (show
                                        (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h)
                                        from (by
                                          unfold nb090AlphaDummy106;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0093 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
                                      ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
                                      ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
                                      ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
                                      ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
                                      ((nb090AlphaDummy099 A), (nb090AlphaDummy100 h)),
                                      ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
                                      ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                      ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                      ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                      ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                      ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                      ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from
                                      (by
                                        unfold nb090AlphaDummy105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0092 A)
                                                0)))) (show (nb090AlphaDummy103 h) ≠
                                        (nb090AlphaDummy106 h) from (by
                                        unfold nb090AlphaDummy106;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0093 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A)
                                        from (by
                                          unfold nb090AlphaDummy105;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0092 A) 0)))) (show
                                        (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h)
                                        from (by
                                          unfold nb090AlphaDummy106;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0093 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
                                      ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
                                      ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
                                      ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
                                      ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
                                      ((nb090AlphaDummy099 A), (nb090AlphaDummy100 h)),
                                      ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
                                      ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                      ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                      ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                      ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                      ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                      ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
