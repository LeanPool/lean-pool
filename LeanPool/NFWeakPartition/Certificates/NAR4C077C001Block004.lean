/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part012`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0002`. -/
@[expose]
noncomputable def nb077SplitAlpha0002 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy073 F I), (nb077AlphaDummy074 x)),
        ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy073 F I))
          (Class.cab (nb077AlphaDummy067 F I)
            (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                (synCphi (Class.cv (nb077AlphaDummy068 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy073 F I))
            (Class.cab (nb077AlphaDummy067 F I)
              (synWrex (nb077AlphaDummy068 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy067 F I))
                  (synCphi (Class.cv (nb077AlphaDummy068 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy074 x))
          (Class.cab (nb077AlphaDummy069 x)
            (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                (synCphi (Class.cv (nb077AlphaDummy070 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy074 x))
            (Class.cab (nb077AlphaDummy069 x)
              (synWrex (nb077AlphaDummy070 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy069 x))
                  (synCphi (Class.cv (nb077AlphaDummy070 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy068 F I) from (by
                      unfold nb077AlphaDummy068;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))))
                  (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy070 x) from (by
                      unfold nb077AlphaDummy070;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0054 x) 1))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy067 F I) from (by
                        unfold nb077AlphaDummy067;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))))
                    (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy069 x) from (by
                        unfold nb077AlphaDummy069;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0054 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy073 F I) from (by
                          unfold nb077AlphaDummy073;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0056 F I) 0))))
                      (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy074 x) from (by
                          unfold nb077AlphaDummy074;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0057 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy071 F I) from (by
                            unfold nb077AlphaDummy071;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0053 F I) 0))))
                        (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy072 x) from (by
                            unfold nb077AlphaDummy072;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0055 x) 0))))
                        (TAlphaVar.there (freshVar_injective (((synCcnv (synC1st))).fv ∪
                              ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
                                  (synC1st))).fv) (by decide)) (freshVar_injective
                            (((synCcnv (synC1st))).fv ∪ ((synCcom
                                  (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                                  (synC1st))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
                      ((Class.cv (nb077AlphaDummy060 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy062 x))).fv ∪
                      ((Class.cv (nb077AlphaDummy063 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy075 F I) from
                            (by
                              unfold nb077AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0058 F I) 0))))
                          (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy077 x) from (by
                              unfold nb077AlphaDummy077;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0059 x) 0))))
                          (TAlphaVar.there (show
                              (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy076 F I) from (by
                                unfold nb077AlphaDummy076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0058 F I) 1))))
                            (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy078 x) from (by
                                unfold nb077AlphaDummy078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0059 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077AlphaDummy068 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077AlphaDummy070 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy082 F I) from
        (by
          unfold nb077AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I) 1)))) (show (nb077AlphaDummy077 x) ≠
        (nb077AlphaDummy085 x) from (by
          unfold nb077AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy081 F I) from (by
          unfold nb077AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I)
                  0)))) (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy084 x) from (by
          unfold nb077AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I) from (by
          unfold nb077AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0060 F I)
                  0)))) (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from (by
          unfold nb077AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0061 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy083 F I), (nb077AlphaDummy086 x)), ((nb077AlphaDummy082 F I),
        (nb077AlphaDummy085 x)), ((nb077AlphaDummy081 F I), (nb077AlphaDummy084 x)),
        ((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)), ((nb077AlphaDummy075 F I),
        (nb077AlphaDummy077 x)), ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
        ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I),
        (nb077AlphaDummy069 x)), ((nb077AlphaDummy073 F I), (nb077AlphaDummy074 x)),
        ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy083 F I), (nb077AlphaDummy086 x)), ((nb077AlphaDummy082 F I),
        (nb077AlphaDummy085 x)), ((nb077AlphaDummy081 F I), (nb077AlphaDummy084 x)),
        ((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)), ((nb077AlphaDummy075 F I),
        (nb077AlphaDummy077 x)), ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
        ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I),
        (nb077AlphaDummy069 x)), ((nb077AlphaDummy073 F I), (nb077AlphaDummy074 x)),
        ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy077
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy093 F I) from
        (by
          unfold
            nb077AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy094 x) from (by
          unfold
            nb077AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy093 F I) from
        (by
          unfold
            nb077AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy094 x) from (by
          unfold
            nb077AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy083
        F I) ≠ (nb077AlphaDummy095 F I) from (by
          unfold
            nb077AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy096 x) from (by
          unfold
            nb077AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy083
        F I) ≠ (nb077AlphaDummy095 F I) from (by
          unfold
            nb077AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy096 x) from (by
          unfold
            nb077AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I)
                                      from (by
                                        unfold nb077AlphaDummy079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0060 F I) 0)))) (show
                                      (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from
                                      (by
                                        unfold nb077AlphaDummy080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0061 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy079 F I),
                                      (nb077AlphaDummy080 x)), ((nb077AlphaDummy075 F I),
                                      (nb077AlphaDummy077 x)), ((nb077AlphaDummy076 F I),
                                      (nb077AlphaDummy078 x)), ((nb077AlphaDummy068 F I),
                                      (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I),
                                      (nb077AlphaDummy069 x)), ((nb077AlphaDummy073 F I),
                                      (nb077AlphaDummy074 x)), ((nb077AlphaDummy071 F I),
                                      (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I),
                                      (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
                                      (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
                                      (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
                                      (nb077AlphaDummy058 x F)),
                                    ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I)
                                    from (by
                                      unfold nb077AlphaDummy079;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0060 F I)
                                              0)))) (show
                                    (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from
                                    (by
                                      unfold nb077AlphaDummy080;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0061 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I)
                                      from (by
                                        unfold nb077AlphaDummy079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0060 F I) 0)))) (show
                                      (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from
                                      (by
                                        unfold nb077AlphaDummy080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0061 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy079 F I),
                                      (nb077AlphaDummy080 x)), ((nb077AlphaDummy075 F I),
                                      (nb077AlphaDummy077 x)), ((nb077AlphaDummy076 F I),
                                      (nb077AlphaDummy078 x)), ((nb077AlphaDummy068 F I),
                                      (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I),
                                      (nb077AlphaDummy069 x)), ((nb077AlphaDummy073 F I),
                                      (nb077AlphaDummy074 x)), ((nb077AlphaDummy071 F I),
                                      (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I),
                                      (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
                                      (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
                                      (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
                                      (nb077AlphaDummy058 x F)),
                                    ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy068 F I) from (by
                        unfold nb077AlphaDummy068;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0052 F I) 1))))
                    (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy070 x) from (by
                        unfold nb077AlphaDummy070;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0054 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy067 F I) from (by
                          unfold nb077AlphaDummy067;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0052 F I) 0))))
                      (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy069 x) from (by
                          unfold nb077AlphaDummy069;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0054 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy073 F I) from (by
                            unfold nb077AlphaDummy073;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0056 F I) 0))))
                        (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy074 x) from (by
                            unfold nb077AlphaDummy074;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0057 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy071 F I) from
                            (by
                              unfold nb077AlphaDummy071;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0053 F I) 0))))
                          (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy072 x) from (by
                              unfold nb077AlphaDummy072;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0055 x) 0))))
                          (TAlphaVar.there (freshVar_injective (((synCcnv (synC1st))).fv ∪
                                ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                      (synCplc (Class.cv (nb077AlphaDummy000 F I))
                                        (synC1c))) (synC1st))).fv) (by decide))
                            (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom
                                    (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                                    (synC1st))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
                        ((Class.cv (nb077AlphaDummy060 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy062 x))).fv ∪
                        ((Class.cv (nb077AlphaDummy063 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy075 F I) from (by
                                unfold nb077AlphaDummy075;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0058 F I) 0))))
                            (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy077 x) from (by
                                unfold nb077AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0059 x) 0))))
                            (TAlphaVar.there (show
                                (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy076 F I) from
                                (by
                                  unfold nb077AlphaDummy076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0058 F I)
                                          1))))
                              (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy078 x) from
                                (by
                                  unfold nb077AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0059 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077AlphaDummy068 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077AlphaDummy070 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy082 F I) from (by
          unfold nb077AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I)
                  1)))) (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy085 x) from (by
          unfold nb077AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy081 F I) from (by
          unfold nb077AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I)
                  0)))) (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy084 x) from (by
          unfold nb077AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy075 F I) ≠
        (nb077AlphaDummy079 F I) from (by
          unfold nb077AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0060 F I)
                  0)))) (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from (by
          unfold nb077AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0061 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy083 F I), (nb077AlphaDummy086 x)), ((nb077AlphaDummy082 F I),
        (nb077AlphaDummy085 x)), ((nb077AlphaDummy081 F I), (nb077AlphaDummy084 x)),
        ((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)), ((nb077AlphaDummy075 F I),
        (nb077AlphaDummy077 x)), ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
        ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I),
        (nb077AlphaDummy069 x)), ((nb077AlphaDummy073 F I), (nb077AlphaDummy074 x)),
        ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy083 F I), (nb077AlphaDummy086 x)), ((nb077AlphaDummy082 F I),
        (nb077AlphaDummy085 x)), ((nb077AlphaDummy081 F I), (nb077AlphaDummy084 x)),
        ((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)), ((nb077AlphaDummy075 F I),
        (nb077AlphaDummy077 x)), ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
        ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I),
        (nb077AlphaDummy069 x)), ((nb077AlphaDummy073 F I), (nb077AlphaDummy074 x)),
        ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy077
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy093 F I) from
        (by
          unfold
            nb077AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy094 x) from (by
          unfold
            nb077AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy093 F I) from
        (by
          unfold
            nb077AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy094 x) from (by
          unfold
            nb077AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy083
        F I) ≠ (nb077AlphaDummy095 F I) from (by
          unfold
            nb077AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy096 x) from (by
          unfold
            nb077AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy083
        F I) ≠ (nb077AlphaDummy095 F I) from (by
          unfold
            nb077AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy096 x) from (by
          unfold
            nb077AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy075 F I) ≠
        (nb077AlphaDummy079 F I) from (by
                                          unfold nb077AlphaDummy079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0060 F I) 0)))) (show
                                        (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x)
                                        from (by
                                          unfold nb077AlphaDummy080;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0061 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)),
                                      ((nb077AlphaDummy075 F I), (nb077AlphaDummy077 x)),
                                      ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
                                      ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)),
                                      ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
                                      ((nb077AlphaDummy073 F I), (nb077AlphaDummy074 x)),
                                      ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
                                      ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                      ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                      ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                      ((nb077AlphaDummy057 F I),
                                        (nb077AlphaDummy058 x F)),
                                      ((nb077AlphaDummy055 F I),
                                        (nb077AlphaDummy056 x F)),
                                      ((nb077AlphaDummy016 F I),
                                        (nb077AlphaDummy018 x F I)),
                                      ((nb077AlphaDummy015 F I),
                                        (nb077AlphaDummy017 x F I)),
                                      ((nb077AlphaDummy013 F I),
                                        (nb077AlphaDummy014 x F I)),
                                      ((nb077AlphaDummy011 F I),
                                        (nb077AlphaDummy012 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I)
                                      from (by
                                        unfold nb077AlphaDummy079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0060 F I) 0)))) (show
                                      (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from
                                      (by
                                        unfold nb077AlphaDummy080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0061 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy075 F I) ≠
        (nb077AlphaDummy079 F I) from (by
                                          unfold nb077AlphaDummy079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0060 F I) 0)))) (show
                                        (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x)
                                        from (by
                                          unfold nb077AlphaDummy080;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0061 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)),
                                      ((nb077AlphaDummy075 F I), (nb077AlphaDummy077 x)),
                                      ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
                                      ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)),
                                      ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
                                      ((nb077AlphaDummy073 F I), (nb077AlphaDummy074 x)),
                                      ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
                                      ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                      ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                      ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                      ((nb077AlphaDummy057 F I),
                                        (nb077AlphaDummy058 x F)),
                                      ((nb077AlphaDummy055 F I),
                                        (nb077AlphaDummy056 x F)),
                                      ((nb077AlphaDummy016 F I),
                                        (nb077AlphaDummy018 x F I)),
                                      ((nb077AlphaDummy015 F I),
                                        (nb077AlphaDummy017 x F I)),
                                      ((nb077AlphaDummy013 F I),
                                        (nb077AlphaDummy014 x F I)),
                                      ((nb077AlphaDummy011 F I),
                                        (nb077AlphaDummy012 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part013`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0003`. -/
@[expose]
noncomputable def nb077SplitAlpha0003 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy101 F I), (nb077AlphaDummy102 x)),
        ((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)),
        ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)),
        ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
        ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)),
        ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy101 F I))
          (synCphi (Class.cv (nb077AlphaDummy068 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy101 F I))
            (synCphi (Class.cv (nb077AlphaDummy068 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy102 x))
          (synCphi (Class.cv (nb077AlphaDummy070 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy102 x))
            (synCphi (Class.cv (nb077AlphaDummy070 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy075 F I) from (by
                      unfold nb077AlphaDummy075;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0058 F I) 0))))
                  (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy077 x) from (by
                      unfold nb077AlphaDummy077;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0059 x) 0))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy076 F I) from (by
                        unfold nb077AlphaDummy076;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0058 F I) 1))))
                    (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy078 x) from (by
                        unfold nb077AlphaDummy078;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0059 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy101 F I) from (by
                          unfold nb077AlphaDummy101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0088 F I) 0))))
                      (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy102 x) from (by
                          unfold nb077AlphaDummy102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0089 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy099 F I) from (by
                            unfold nb077AlphaDummy099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0086 F I) 0))))
                        (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy100 x) from (by
                            unfold nb077AlphaDummy100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0087 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077AlphaDummy068 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy070 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy082 F I)
                                      from (by
                                        unfold nb077AlphaDummy082;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0062 F I) 1)))) (show
                                      (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy085 x) from
                                      (by
                                        unfold nb077AlphaDummy085;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0063 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy075 F I) ≠
        (nb077AlphaDummy081 F I) from (by
                                          unfold nb077AlphaDummy081;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0062 F I) 0)))) (show
                                        (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy084 x)
                                        from (by
                                          unfold nb077AlphaDummy084;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0063 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy075 F I) ≠
        (nb077AlphaDummy079 F I) from (by
          unfold nb077AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0060 F I) 0)))) (show (nb077AlphaDummy077 x) ≠
        (nb077AlphaDummy080 x) from (by
          unfold nb077AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0061 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb077AlphaDummy083 F I),
        (nb077AlphaDummy086 x)), ((nb077AlphaDummy082 F I), (nb077AlphaDummy085 x)),
                                        ((nb077AlphaDummy081 F I),
        (nb077AlphaDummy084 x)), ((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)),
                                        ((nb077AlphaDummy075 F I),
        (nb077AlphaDummy077 x)), ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
                                        ((nb077AlphaDummy101 F I),
        (nb077AlphaDummy102 x)), ((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)),
                                        ((nb077AlphaDummy068 F I),
        (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
                                        ((nb077AlphaDummy097 F I),
        (nb077AlphaDummy098 x)), ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
                                        ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                        ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                                        ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy089 F I) from (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy089 F I) from (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy089 F I) from (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb077AlphaDummy083 F I),
        (nb077AlphaDummy086 x)), ((nb077AlphaDummy082 F I), (nb077AlphaDummy085 x)),
        ((nb077AlphaDummy081 F I), (nb077AlphaDummy084 x)), ((nb077AlphaDummy079 F I),
        (nb077AlphaDummy080 x)), ((nb077AlphaDummy075 F I), (nb077AlphaDummy077 x)),
        ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)), ((nb077AlphaDummy101 F I),
        (nb077AlphaDummy102 x)), ((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)),
        ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I),
        (nb077AlphaDummy069 x)), ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)),
        ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy075 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy093 F I) from (by
          unfold
            nb077AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy094 x) from (by
          unfold
            nb077AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy093 F I) from (by
          unfold
            nb077AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy094 x) from (by
          unfold
            nb077AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy083 F I) ≠ (nb077AlphaDummy095 F I) from (by
          unfold
            nb077AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy096 x) from (by
          unfold
            nb077AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy083 F I) ≠ (nb077AlphaDummy095 F I) from (by
          unfold
            nb077AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy096 x) from (by
          unfold
            nb077AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I) from (by
                                unfold nb077AlphaDummy079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0060 F I) 0))))
                            (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from (by
                                unfold nb077AlphaDummy080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)),
                            ((nb077AlphaDummy075 F I), (nb077AlphaDummy077 x)),
                            ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
                            ((nb077AlphaDummy101 F I), (nb077AlphaDummy102 x)),
                            ((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)),
                            ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)),
                            ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
                            ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)),
                            ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
                            ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                            ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                            ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                            ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                            ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                            ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                            ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                            ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                            ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I) from
                            (by
                              unfold nb077AlphaDummy079;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0060 F I) 0))))
                          (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from (by
                              unfold nb077AlphaDummy080;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I) from (by
                                unfold nb077AlphaDummy079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0060 F I) 0))))
                            (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from (by
                                unfold nb077AlphaDummy080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)),
                            ((nb077AlphaDummy075 F I), (nb077AlphaDummy077 x)),
                            ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
                            ((nb077AlphaDummy101 F I), (nb077AlphaDummy102 x)),
                            ((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)),
                            ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)),
                            ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
                            ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)),
                            ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
                            ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                            ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                            ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                            ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                            ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                            ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                            ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                            ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                            ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy075 F I) from (by
                        unfold nb077AlphaDummy075;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0058 F I) 0))))
                    (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy077 x) from (by
                        unfold nb077AlphaDummy077;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0059 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy076 F I) from (by
                          unfold nb077AlphaDummy076;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0058 F I) 1))))
                      (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy078 x) from (by
                          unfold nb077AlphaDummy078;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0059 x) 1))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy101 F I) from (by
                            unfold nb077AlphaDummy101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0088 F I) 0))))
                        (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy102 x) from (by
                            unfold nb077AlphaDummy102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0089 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy068 F I) ≠ (nb077AlphaDummy099 F I) from
                            (by
                              unfold nb077AlphaDummy099;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0086 F I) 0))))
                          (show (nb077AlphaDummy070 x) ≠ (nb077AlphaDummy100 x) from (by
                              unfold nb077AlphaDummy100;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0087 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077AlphaDummy068 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy070 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077AlphaDummy075 F I) ≠
        (nb077AlphaDummy082 F I) from (by
                                          unfold nb077AlphaDummy082;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0062 F I) 1)))) (show
                                        (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy085 x)
                                        from (by
                                          unfold nb077AlphaDummy085;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0063 x) 1))))
                                      (TAlphaVar.there (show (nb077AlphaDummy075 F I) ≠
        (nb077AlphaDummy081 F I) from (by
          unfold nb077AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0062 F I) 0)))) (show (nb077AlphaDummy077 x) ≠
        (nb077AlphaDummy084 x) from (by
          unfold nb077AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I) from (by
          unfold nb077AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0060 F I) 0)))) (show (nb077AlphaDummy077 x) ≠
        (nb077AlphaDummy080 x) from (by
          unfold nb077AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0061 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb077AlphaDummy083 F I),
        (nb077AlphaDummy086 x)), ((nb077AlphaDummy082 F I), (nb077AlphaDummy085 x)),
        ((nb077AlphaDummy081 F I), (nb077AlphaDummy084 x)), ((nb077AlphaDummy079 F I),
        (nb077AlphaDummy080 x)), ((nb077AlphaDummy075 F I), (nb077AlphaDummy077 x)),
        ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)), ((nb077AlphaDummy101 F I),
        (nb077AlphaDummy102 x)), ((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)),
        ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I),
        (nb077AlphaDummy069 x)), ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)),
        ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy082 F
        I) ≠ (nb077AlphaDummy089 F I) from (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0066
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0064
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠ (nb077AlphaDummy089 F I) from
        (by
          unfold
            nb077AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0070
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy090 x) from (by
          unfold
            nb077AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy087 F I) from (by
          unfold
            nb077AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0068
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy088 x) from (by
          unfold
            nb077AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy083 F I), (nb077AlphaDummy086 x)), ((nb077AlphaDummy082 F I),
        (nb077AlphaDummy085 x)), ((nb077AlphaDummy081 F I), (nb077AlphaDummy084 x)),
        ((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)), ((nb077AlphaDummy075 F I),
        (nb077AlphaDummy077 x)), ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
        ((nb077AlphaDummy101 F I), (nb077AlphaDummy102 x)), ((nb077AlphaDummy099 F I),
        (nb077AlphaDummy100 x)), ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)),
        ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)), ((nb077AlphaDummy097 F I),
        (nb077AlphaDummy098 x)), ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy082 F
        I) ≠ (nb077AlphaDummy093 F I) from (by
          unfold
            nb077AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy094 x) from (by
          unfold
            nb077AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠ (nb077AlphaDummy093 F I) from
        (by
          unfold
            nb077AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0074
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy094 x) from (by
          unfold
            nb077AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0075
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy082 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0072
                    F I)
                  0)))) (show (nb077AlphaDummy085 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0073
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy075
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy077 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy083 F
        I) ≠ (nb077AlphaDummy095 F I) from (by
          unfold
            nb077AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy096 x) from (by
          unfold
            nb077AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy083 F
        I) ≠ (nb077AlphaDummy095 F I) from (by
          unfold
            nb077AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0078
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy096 x) from (by
          unfold
            nb077AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0079
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy083 F I) ≠
        (nb077AlphaDummy091 F I) from (by
          unfold
            nb077AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0076
                    F I)
                  0)))) (show (nb077AlphaDummy086 x) ≠ (nb077AlphaDummy092 x) from (by
          unfold
            nb077AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0077
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I) from
                                (by
                                  unfold nb077AlphaDummy079;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0060 F I)
                                          0))))
                              (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from
                                (by
                                  unfold nb077AlphaDummy080;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)),
                              ((nb077AlphaDummy075 F I), (nb077AlphaDummy077 x)),
                              ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
                              ((nb077AlphaDummy101 F I), (nb077AlphaDummy102 x)),
                              ((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)),
                              ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)),
                              ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
                              ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)),
                              ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
                              ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                              ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                              ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                              ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                              ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                              ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                              ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                              ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                              ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I) from (by
                                unfold nb077AlphaDummy079;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0060 F I) 0))))
                            (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from (by
                                unfold nb077AlphaDummy080;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy075 F I) ≠ (nb077AlphaDummy079 F I) from
                                (by
                                  unfold nb077AlphaDummy079;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0060 F I)
                                          0))))
                              (show (nb077AlphaDummy077 x) ≠ (nb077AlphaDummy080 x) from
                                (by
                                  unfold nb077AlphaDummy080;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0061 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy079 F I), (nb077AlphaDummy080 x)),
                              ((nb077AlphaDummy075 F I), (nb077AlphaDummy077 x)),
                              ((nb077AlphaDummy076 F I), (nb077AlphaDummy078 x)),
                              ((nb077AlphaDummy101 F I), (nb077AlphaDummy102 x)),
                              ((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)),
                              ((nb077AlphaDummy068 F I), (nb077AlphaDummy070 x)),
                              ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
                              ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)),
                              ((nb077AlphaDummy071 F I), (nb077AlphaDummy072 x)),
                              ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                              ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                              ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                              ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                              ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                              ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                              ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                              ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                              ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part014`. -/


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

theorem nb077_compact_fv_empty_0100 (F : Class) (I : Class) :
    (nb077AlphaDummy061 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0101 (x : Var) :
    (nb077AlphaDummy064 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
