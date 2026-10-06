/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C077C001Part048

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part049`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0035`. -/
@[expose]
noncomputable def nb077SplitAlpha0035 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy055 F I)) (synCnin
            (synCcom (synCcnv (synC1st)) (synCcom
                (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                  (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy055 F I)) (synCnin
              (synCcom (synCcnv (synC1st)) (synCcom
                  (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) (synC1st)))
              (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy056 x F)) (synCnin
            (synCcom (synCcnv (synC1st))
              (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
            (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy056 x F)) (synCnin
              (synCcom (synCcnv (synC1st))
                (synCcom (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) (synC1st)))
              (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (Ne.symm (show
                                (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy065 F I) from
                                (by
                                  unfold nb077AlphaDummy065;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0050 F I)
                                          0))))) (Ne.symm
                              (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy066 x) from
                                (by
                                  unfold nb077AlphaDummy066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0051 x) 0)))))
                            (TAlphaVar.there (Ne.symm (show (nb077AlphaDummy059 F I) ≠
                                    (nb077AlphaDummy065 F I) from (by
                                    unfold nb077AlphaDummy065;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0048 F I)
                                            0))))) (Ne.symm (show
                                  (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy066 x) from (by
                                    unfold nb077AlphaDummy066;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0049 x)
                                            0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb077SplitAlpha0020 x F I)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy068 F I) from (by
          unfold nb077AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080 F
                    I)
                  1)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy070 x) from (by
          unfold nb077AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082 x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy067 F I) from (by
          unfold nb077AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy069 x) from (by
          unfold nb077AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy097 F I) from (by
          unfold nb077AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy098 x) from (by
          unfold nb077AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy071 F I) from (by
          unfold
            nb077AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy072 x) from (by
          unfold
            nb077AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0021 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)), ((nb077AlphaDummy068 F I),
        (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
        ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)), ((nb077AlphaDummy071 F I),
        (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy068 F I) from
        (by
          unfold nb077AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080 F
                    I)
                  1)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy070 x) from (by
          unfold nb077AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082 x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy067 F I) from (by
          unfold nb077AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy069 x) from (by
          unfold nb077AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy097 F I) from (by
          unfold nb077AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy098 x) from (by
          unfold nb077AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy071 F I) from (by
          unfold
            nb077AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy072 x) from (by
          unfold
            nb077AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0021 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)), ((nb077AlphaDummy068 F I),
        (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
        ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)), ((nb077AlphaDummy071 F I),
        (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb077SplitAlpha0022 x F I)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy104 F I) from (by
          unfold nb077AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  1)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy106 x) from (by
          unfold nb077AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy103 F I) from (by
          unfold
            nb077AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy105 x) from (by
          unfold
            nb077AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy133 F I) from (by
          unfold
            nb077AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy134 x) from (by
          unfold
            nb077AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy107 F I) from (by
          unfold
            nb077AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy108 x) from (by
          unfold
            nb077AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0121
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0023 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)), ((nb077AlphaDummy104 F I),
        (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
        ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)), ((nb077AlphaDummy107 F I),
        (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F
        I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x
        F I)), ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F
        I), (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy104 F I) from (by
          unfold nb077AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  1)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy106 x) from (by
          unfold nb077AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy103 F I) from (by
          unfold
            nb077AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy105 x) from (by
          unfold
            nb077AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy133 F I) from (by
          unfold
            nb077AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy134 x) from (by
          unfold
            nb077AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy107 F I) from (by
          unfold
            nb077AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy108 x) from (by
          unfold
            nb077AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0121
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0023 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)), ((nb077AlphaDummy104 F I),
        (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
        ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)), ((nb077AlphaDummy107 F I),
        (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F
        I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x
        F I)), ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F
        I), (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (Ne.symm (show
        (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy145 F I) from (by
          unfold nb077AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0130 F I)
                  0))))) (Ne.symm (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy146 x)
        from (by
          unfold nb077AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0131 x) 0))))) (TAlphaVar.there (Ne.symm (show
        (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy145 F I) from (by
          unfold nb077AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0128 F I)
                  0))))) (Ne.symm (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy146 x)
        from (by
          unfold nb077AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0129 x)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0024 x F I)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy148 F I) from
        (by
          unfold
            nb077AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  1)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy150 x) from (by
          unfold
            nb077AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy147 F I) from (by
          unfold
            nb077AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy149 x) from (by
          unfold
            nb077AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy177 F I) from (by
          unfold
            nb077AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0164
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy178 x) from (by
          unfold
            nb077AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0165
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy151 F I) from (by
          unfold
            nb077AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0161
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy152 x) from (by
          unfold
            nb077AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0163
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0025 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)), ((nb077AlphaDummy148 F I),
        (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
        ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)), ((nb077AlphaDummy151 F I),
        (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055
        F I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018
        x F I)), ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004
        F I), (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy140
        F I) ≠ (nb077AlphaDummy148 F I) from (by
          unfold
            nb077AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  1)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy150 x) from (by
          unfold
            nb077AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy147 F I) from (by
          unfold
            nb077AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy149 x) from (by
          unfold
            nb077AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy177 F I) from (by
          unfold
            nb077AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0164
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy178 x) from (by
          unfold
            nb077AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0165
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy151 F I) from (by
          unfold
            nb077AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0161
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy152 x) from (by
          unfold
            nb077AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0163
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0025 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)), ((nb077AlphaDummy148 F I),
        (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
        ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)), ((nb077AlphaDummy151 F I),
        (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055
        F I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018
        x F I)), ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004
        F I), (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex
                                      (TAlphaWff.neg (nb077SplitAlpha0032 x F I))))))))
                          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.neg (nb077SplitAlpha0033 x F I)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy312 F I) from (by
          unfold nb077AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  1)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy314 x) from (by
          unfold nb077AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy311 F I) from (by
          unfold
            nb077AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy313 x) from (by
          unfold
            nb077AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy341 F I) from (by
          unfold
            nb077AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy342 x) from (by
          unfold
            nb077AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy315 F I) from (by
          unfold
            nb077AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy316 x) from (by
          unfold
            nb077AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0339
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv
        (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) (by decide))
        (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt x (synCvv)
        (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy061 F I))).fv ∪ ((Class.cv (nb077AlphaDummy060 F
        I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy064 x))).fv ∪
        ((Class.cv (nb077AlphaDummy063 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0034 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb077AlphaDummy343 F I),
        (nb077AlphaDummy344 x)), ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
        ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)), ((nb077AlphaDummy341 F I),
        (nb077AlphaDummy342 x)), ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x
        F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F
        I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x
        F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy312 F I) from (by
          unfold nb077AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  1)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy314 x) from (by
          unfold nb077AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy311 F I) from (by
          unfold
            nb077AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy313 x) from (by
          unfold
            nb077AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy341 F I) from (by
          unfold
            nb077AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy342 x) from (by
          unfold
            nb077AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy315 F I) from (by
          unfold
            nb077AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy316 x) from (by
          unfold
            nb077AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0339
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv
        (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) (by decide))
        (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt x (synCvv)
        (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy061 F I))).fv ∪ ((Class.cv (nb077AlphaDummy060 F
        I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy064 x))).fv ∪
        ((Class.cv (nb077AlphaDummy063 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0034 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb077AlphaDummy343 F I),
        (nb077AlphaDummy344 x)), ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
        ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)), ((nb077AlphaDummy341 F I),
        (nb077AlphaDummy342 x)), ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x
        F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F
        I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x
        F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                              [((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                                ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                                ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                                ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                                ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                                ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                                ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                                ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                              (synCcnv (synC1st)) (nb077WppRefl0124 x F I))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn
                [((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                  ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                  ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                  ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                  ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                  ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                  ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))
                (nb077WppRefl0125 x F I))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                            (TAlphaVar.there (Ne.symm (show (nb077AlphaDummy060 F I) ≠
                                    (nb077AlphaDummy065 F I) from (by
                                    unfold nb077AlphaDummy065;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0050 F I)
                                            0))))) (Ne.symm (show
                                  (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy066 x) from (by
                                    unfold nb077AlphaDummy066;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0051 x)
                                            0))))) (TAlphaVar.there (Ne.symm (show
                                    (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy065 F I)
                                    from (by
                                      unfold nb077AlphaDummy065;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0048 F I)
                                              0))))) (Ne.symm (show
                                    (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy066 x) from
                                    (by
                                      unfold nb077AlphaDummy066;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0049 x)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb077SplitAlpha0020 x F I)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy068 F I) from
        (by
          unfold nb077AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  1)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy070 x) from (by
          unfold nb077AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy067 F I) from (by
          unfold nb077AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy069 x) from (by
          unfold nb077AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy097 F I) from (by
          unfold
            nb077AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy098 x) from (by
          unfold
            nb077AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy071 F I) from (by
          unfold
            nb077AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy072 x) from (by
          unfold
            nb077AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0021 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)), ((nb077AlphaDummy068 F I),
        (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
        ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)), ((nb077AlphaDummy071 F I),
        (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F
        I), (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F
        I)), ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy068 F I) from (by
          unfold nb077AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  1)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy070 x) from (by
          unfold nb077AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy067 F I) from (by
          unfold nb077AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy069 x) from (by
          unfold nb077AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy097 F I) from (by
          unfold
            nb077AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy098 x) from (by
          unfold
            nb077AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy071 F I) from (by
          unfold
            nb077AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy072 x) from (by
          unfold
            nb077AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0021 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy099 F I), (nb077AlphaDummy100 x)), ((nb077AlphaDummy068 F I),
        (nb077AlphaDummy070 x)), ((nb077AlphaDummy067 F I), (nb077AlphaDummy069 x)),
        ((nb077AlphaDummy097 F I), (nb077AlphaDummy098 x)), ((nb077AlphaDummy071 F I),
        (nb077AlphaDummy072 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F
        I), (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F
        I)), ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))] (synCcompl
        (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0022 x F I))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy104 F I) from
        (by
          unfold
            nb077AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  1)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy106 x) from (by
          unfold
            nb077AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy103 F I) from (by
          unfold
            nb077AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy105 x) from (by
          unfold
            nb077AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy133 F I) from (by
          unfold
            nb077AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy134 x) from (by
          unfold
            nb077AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy107 F I) from (by
          unfold
            nb077AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy108 x) from (by
          unfold
            nb077AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0121
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0023 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)), ((nb077AlphaDummy104 F I),
        (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
        ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)), ((nb077AlphaDummy107 F I),
        (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055
        F I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018
        x F I)), ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004
        F I), (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy061 F I) ≠ (nb077AlphaDummy104 F I) from (by
          unfold
            nb077AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  1)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy106 x) from (by
          unfold
            nb077AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy103 F I) from (by
          unfold
            nb077AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy105 x) from (by
          unfold
            nb077AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy133 F I) from (by
          unfold
            nb077AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy134 x) from (by
          unfold
            nb077AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy061 F I) ≠
        (nb077AlphaDummy107 F I) from (by
          unfold
            nb077AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077AlphaDummy064 x) ≠ (nb077AlphaDummy108 x) from (by
          unfold
            nb077AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0121
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy061 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy062 x))).fv ∪ ((Class.cv (nb077AlphaDummy064 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0023 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)), ((nb077AlphaDummy104 F I),
        (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
        ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)), ((nb077AlphaDummy107 F I),
        (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055
        F I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018
        x F I)), ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004
        F I), (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (Ne.symm (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy145 F I) from (by
          unfold nb077AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0130 F I)
                  0))))) (Ne.symm (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy146 x)
        from (by
          unfold nb077AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0131 x)
                  0))))) (TAlphaVar.there (Ne.symm (show (nb077AlphaDummy139 F I) ≠
        (nb077AlphaDummy145 F I) from (by
          unfold nb077AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0128 F I)
                  0))))) (Ne.symm (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy146 x)
        from (by
          unfold nb077AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0129 x)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0024 x F I)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠ (nb077AlphaDummy148 F I) from
        (by
          unfold
            nb077AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  1)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy150 x) from (by
          unfold
            nb077AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy147 F I) from (by
          unfold
            nb077AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy149 x) from (by
          unfold
            nb077AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy177 F I) from (by
          unfold
            nb077AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0164
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy178 x) from (by
          unfold
            nb077AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0165
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy151 F I) from (by
          unfold
            nb077AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0161
                    F
                    I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy152 x) from (by
          unfold
            nb077AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0163
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0025 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)), ((nb077AlphaDummy148 F I),
        (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
        ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)), ((nb077AlphaDummy151 F I),
        (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055
        F I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018
        x F I)), ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004
        F I), (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy140
        F I) ≠ (nb077AlphaDummy148 F I) from (by
          unfold
            nb077AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  1)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy150 x) from (by
          unfold
            nb077AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy147 F I) from (by
          unfold
            nb077AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy149 x) from (by
          unfold
            nb077AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy177 F I) from (by
          unfold
            nb077AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0164
                    F I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy178 x) from (by
          unfold
            nb077AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0165
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy140 F I) ≠
        (nb077AlphaDummy151 F I) from (by
          unfold
            nb077AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0161
                    F
                    I)
                  0)))) (show (nb077AlphaDummy143 x) ≠ (nb077AlphaDummy152 x) from (by
          unfold
            nb077AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0163
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy140 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy142 x))).fv ∪ ((Class.cv (nb077AlphaDummy143 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077SplitAlpha0025 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)), ((nb077AlphaDummy148 F I),
        (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
        ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)), ((nb077AlphaDummy151 F I),
        (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055
        F I), (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018
        x F I)), ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004
        F I), (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex (TAlphaWff.neg
        (nb077SplitAlpha0032 x F I)))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0033 x F I))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy312 F I) from
        (by
          unfold
            nb077AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  1)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy314 x) from (by
          unfold
            nb077AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy311 F I) from (by
          unfold
            nb077AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy313 x) from (by
          unfold
            nb077AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy341 F I) from (by
          unfold
            nb077AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy342 x) from (by
          unfold
            nb077AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy315 F I) from (by
          unfold
            nb077AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy316 x) from (by
          unfold
            nb077AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0339
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv
        (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) (by decide))
        (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt x (synCvv)
        (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy061 F I))).fv ∪ ((Class.cv (nb077AlphaDummy060 F
        I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy064 x))).fv ∪
        ((Class.cv (nb077AlphaDummy063 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0034 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb077AlphaDummy343 F I),
        (nb077AlphaDummy344 x)), ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
        ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)), ((nb077AlphaDummy341 F I),
        (nb077AlphaDummy342 x)), ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I), (nb077AlphaDummy056
        x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001
        F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I), (nb077AlphaDummy005
        x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy060 F I) ≠ (nb077AlphaDummy312 F I) from (by
          unfold
            nb077AlphaDummy312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  1)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy314 x) from (by
          unfold
            nb077AlphaDummy314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy311 F I) from (by
          unfold
            nb077AlphaDummy311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy313 x) from (by
          unfold
            nb077AlphaDummy313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy341 F I) from (by
          unfold
            nb077AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy342 x) from (by
          unfold
            nb077AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy060 F I) ≠
        (nb077AlphaDummy315 F I) from (by
          unfold
            nb077AlphaDummy315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077AlphaDummy063 x) ≠ (nb077AlphaDummy316 x) from (by
          unfold
            nb077AlphaDummy316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0339
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synC1st))).fv ∪
        ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv
        (nb077AlphaDummy000 F I)) (synC1c))) (synC1st))).fv) (by decide))
        (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt x (synCvv)
        (synCplc (Class.cv x) (synC1c))) (synC1st))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy061 F I))).fv ∪ ((Class.cv (nb077AlphaDummy060 F
        I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy064 x))).fv ∪
        ((Class.cv (nb077AlphaDummy063 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0034 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb077AlphaDummy343 F I),
        (nb077AlphaDummy344 x)), ((nb077AlphaDummy312 F I), (nb077AlphaDummy314 x)),
        ((nb077AlphaDummy311 F I), (nb077AlphaDummy313 x)), ((nb077AlphaDummy341 F I),
        (nb077AlphaDummy342 x)), ((nb077AlphaDummy315 F I), (nb077AlphaDummy316 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I), (nb077AlphaDummy056
        x F)), ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001
        F I), (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I), (nb077AlphaDummy005
        x F I))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                [((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                                  ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                  ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                  ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                  ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                                  ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                                  ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                                  ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                                  ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                                  ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                                  ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                (synCcnv (synC1st)) (nb077WppRefl0124 x F I))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfReflOn
                  [((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                    ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                    ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                    ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                    ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                    ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                    ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                  (synCcom (synCcnv (synC2nd)) (synCcom F (synC2nd)))
                  (nb077WppRefl0125 x F I)))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part050`. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_frec`. -/
@[expose]
noncomputable def nominalDfFrec (x : Var) (F : Class) (I : Class) (__dv_F_x : x ∉ F.fv)
    (__dv_I_x : x ∉ I.fv) :
    Nominal.NPrf
      (.classEq (synCfrec F I) (synCclos1 (synCsn (synCop (synC0c) I))
          (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfReflOn [((nb077AlphaDummy009 F I),
        (nb077AlphaDummy010 x F I)), ((nb077AlphaDummy007 F I),
        (nb077AlphaDummy008 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCsn (synCop (synC0c) I))
                                      (nb077WppRefl0000 x F I))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy009 F I) from (by
          unfold nb077AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0002 F I) 0)))) (show (nb077AlphaDummy002 x F I) ≠
        (nb077AlphaDummy010 x F I) from (by
          unfold nb077AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0003 x F I) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy001 F I) ≠ (nb077AlphaDummy007 F I) from (by
          unfold nb077AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0000 F I) 0)))) (show (nb077AlphaDummy002 x F I) ≠
        (nb077AlphaDummy008 x F I) from (by
          unfold nb077AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0001 x F I) 0)))) (TAlphaVar.here _ _ _)))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfReflOn [((nb077AlphaDummy009 F I),
        (nb077AlphaDummy010 x F I)), ((nb077AlphaDummy007 F I),
        (nb077AlphaDummy008 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synCsn (synCop (synC0c) I))
                                      (nb077WppRefl0000 x F I))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy009 F I) from (by
          unfold nb077AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0002 F I) 0)))) (show (nb077AlphaDummy002 x F I) ≠
        (nb077AlphaDummy010 x F I) from (by
          unfold nb077AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0003 x F I) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy001 F I) ≠ (nb077AlphaDummy007 F I) from (by
          unfold nb077AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0000 F I) 0)))) (show (nb077AlphaDummy002 x F I) ≠
        (nb077AlphaDummy008 x F I) from (by
          unfold nb077AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0001 x F I) 0)))) (TAlphaVar.here _ _ _))))))))))))
                    (TAlphaClass.reflOfReflOn
                      [((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                      (synCsn (synCop (synC0c) I)) (nb077WppRefl0001 x F I)))
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy001 F I) ≠ (nb077AlphaDummy016 F I) from (by
          unfold nb077AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0008 F I)
                  1)))) (show (nb077AlphaDummy002 x F I) ≠ (nb077AlphaDummy018 x F I) from
        (by
          unfold nb077AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0009 x F I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy015 F I) from (by
          unfold nb077AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0008 F I)
                  0)))) (show (nb077AlphaDummy002 x F I) ≠ (nb077AlphaDummy017 x F I) from
        (by
          unfold nb077AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0009 x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy013 F I) from (by
          unfold nb077AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0006 F
                    I)
                  0)))) (show (nb077AlphaDummy002 x F I) ≠ (nb077AlphaDummy014 x F I) from
        (by
          unfold nb077AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0007 x
                    F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy011 F I) from (by
          unfold nb077AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0004
                    F I)
                  0)))) (show (nb077AlphaDummy002 x F I) ≠ (nb077AlphaDummy012 x F I) from
        (by
          unfold nb077AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0005
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0000 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy020 F I) from (by
          unfold
            nb077AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy022 x F I) from
        (by
          unfold
            nb077AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy019 F I) from (by
          unfold
            nb077AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy021 x F I) from
        (by
          unfold
            nb077AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy049 F I) from (by
          unfold
            nb077AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy050 x F I) from
        (by
          unfold
            nb077AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy023 F I) from (by
          unfold
            nb077AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy024 x F I) from
        (by
          unfold
            nb077AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCpprod (synCmpt
        (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv (nb077AlphaDummy000 F I))
        (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv) (by
          decide)) (freshVar_injective (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv
        x) (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪ ((Class.cv (nb077AlphaDummy017 x F
        I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.neg (nb077SplitAlpha0001 x F I))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠ (nb077AlphaDummy020 F I) from
        (by
          unfold
            nb077AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy022 x F I) from
        (by
          unfold
            nb077AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy019 F I) from (by
          unfold
            nb077AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy021 x F I) from
        (by
          unfold
            nb077AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy049 F I) from (by
          unfold
            nb077AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy050 x F I) from
        (by
          unfold
            nb077AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy023 F I) from (by
          unfold
            nb077AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy024 x F I) from
        (by
          unfold
            nb077AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCpprod (synCmpt
        (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv (nb077AlphaDummy000 F I))
        (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv) (by
          decide)) (freshVar_injective (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv
        x) (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪ ((Class.cv (nb077AlphaDummy017 x F
        I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.neg (nb077SplitAlpha0001 x F I)))))))))))))))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0017 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0017 x F I))))))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy013 F I) from (by
          unfold nb077AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0006 F I) 0)))) (show (nb077AlphaDummy002 x F I) ≠
        (nb077AlphaDummy014 x F I) from (by
          unfold nb077AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0007 x F I) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy001 F I) ≠ (nb077AlphaDummy011 F I) from (by
          unfold nb077AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0004 F I) 0)))) (show (nb077AlphaDummy002 x F I) ≠
        (nb077AlphaDummy012 x F I) from (by
          unfold nb077AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0005 x F I) 0)))) (TAlphaVar.here _ _ _)))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy001 F I) ≠ (nb077AlphaDummy016 F I) from (by
          unfold nb077AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0008 F I)
                  1)))) (show (nb077AlphaDummy002 x F I) ≠ (nb077AlphaDummy018 x F I) from
        (by
          unfold nb077AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0009 x F I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy015 F I) from (by
          unfold nb077AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0008 F I)
                  0)))) (show (nb077AlphaDummy002 x F I) ≠ (nb077AlphaDummy017 x F I) from
        (by
          unfold nb077AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0009 x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy013 F I) from (by
          unfold nb077AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0006 F
                    I)
                  0)))) (show (nb077AlphaDummy002 x F I) ≠ (nb077AlphaDummy014 x F I) from
        (by
          unfold nb077AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0007 x
                    F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy011 F I) from (by
          unfold nb077AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0004
                    F I)
                  0)))) (show (nb077AlphaDummy002 x F I) ≠ (nb077AlphaDummy012 x F I) from
        (by
          unfold nb077AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0005
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0000 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy020 F I) from (by
          unfold
            nb077AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy022 x F I) from
        (by
          unfold
            nb077AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy019 F I) from (by
          unfold
            nb077AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy021 x F I) from
        (by
          unfold
            nb077AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy049 F I) from (by
          unfold
            nb077AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy050 x F I) from
        (by
          unfold
            nb077AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy023 F I) from (by
          unfold
            nb077AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy024 x F I) from
        (by
          unfold
            nb077AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCpprod (synCmpt
        (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv (nb077AlphaDummy000 F I))
        (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv) (by
          decide)) (freshVar_injective (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv
        x) (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪ ((Class.cv (nb077AlphaDummy017 x F
        I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.neg (nb077SplitAlpha0001 x F I))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠ (nb077AlphaDummy020 F I) from
        (by
          unfold
            nb077AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy022 x F I) from
        (by
          unfold
            nb077AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy019 F I) from (by
          unfold
            nb077AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy021 x F I) from
        (by
          unfold
            nb077AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy049 F I) from (by
          unfold
            nb077AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy050 x F I) from
        (by
          unfold
            nb077AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy023 F I) from (by
          unfold
            nb077AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F
                    I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy024 x F I) from
        (by
          unfold
            nb077AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCpprod (synCmpt
        (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv (nb077AlphaDummy000 F I))
        (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv) (by
          decide)) (freshVar_injective (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv
        x) (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy016 F I))).fv ∪
        ((Class.cv (nb077AlphaDummy015 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy018 x F I))).fv ∪ ((Class.cv (nb077AlphaDummy017 x F
        I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.neg (nb077SplitAlpha0001 x F I)))))))))))))))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0017 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077SplitAlpha0017 x F I))))))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
        (nb077AlphaDummy013 F I) from (by
          unfold nb077AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0006 F I) 0)))) (show (nb077AlphaDummy002 x F I) ≠
        (nb077AlphaDummy014 x F I) from (by
          unfold nb077AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0007 x F I) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy001 F I) ≠ (nb077AlphaDummy011 F I) from (by
          unfold nb077AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0004 F I) 0)))) (show (nb077AlphaDummy002 x F I) ≠
        (nb077AlphaDummy012 x F I) from (by
          unfold nb077AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0005 x F I) 0)))) (TAlphaVar.here _ _ _))))))))))))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy001 F I) ≠
                                    (nb077AlphaDummy016 F I) from (by
                                    unfold nb077AlphaDummy016;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0008 F I)
                                            1)))) (show (nb077AlphaDummy002 x F I) ≠
                                    (nb077AlphaDummy018 x F I) from (by
                                    unfold nb077AlphaDummy018;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0009 x F I)
                                            1)))) (TAlphaVar.there (show
                                    (nb077AlphaDummy001 F I) ≠ (nb077AlphaDummy015 F I)
                                    from (by
                                      unfold nb077AlphaDummy015;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0008 F I)
                                              0)))) (show (nb077AlphaDummy002 x F I) ≠
                                      (nb077AlphaDummy017 x F I) from (by
                                      unfold nb077AlphaDummy017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0009 x F I) 0))))
                                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (nb077SplitAlpha0018 x F I)
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy015 F I) ≠ (nb077AlphaDummy020 F I) from (by
          unfold nb077AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy022 x F I) from
        (by
          unfold nb077AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy019 F I) from (by
          unfold
            nb077AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy021 x F I) from
        (by
          unfold
            nb077AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy049 F I) from (by
          unfold
            nb077AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy050 x F I) from
        (by
          unfold
            nb077AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy023 F I) from (by
          unfold
            nb077AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy024 x F I) from
        (by
          unfold
            nb077AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCpprod (synCmpt
        (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv (nb077AlphaDummy000 F I))
        (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv) (by decide))
        (freshVar_injective (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x)
        (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb077SplitAlpha0019 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠ (nb077AlphaDummy020 F I) from
        (by
          unfold nb077AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy022 x F I) from
        (by
          unfold nb077AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F I)
                  1)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy019 F I) from (by
          unfold
            nb077AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy021 x F I) from
        (by
          unfold
            nb077AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy049 F I) from (by
          unfold
            nb077AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy050 x F I) from
        (by
          unfold
            nb077AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy015 F I) ≠
        (nb077AlphaDummy023 F I) from (by
          unfold
            nb077AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F I)
                  0)))) (show (nb077AlphaDummy017 x F I) ≠ (nb077AlphaDummy024 x F I) from
        (by
          unfold
            nb077AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCpprod (synCmpt
        (nb077AlphaDummy000 F I) (synCvv) (synCplc (Class.cv (nb077AlphaDummy000 F I))
        (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy001 F I))).fv) (by decide))
        (freshVar_injective (((synCpprod (synCmpt x (synCvv) (synCplc (Class.cv x)
        (synC1c))) F)).fv ∪ ((Class.cv (nb077AlphaDummy002 x F I))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb077SplitAlpha0019 x F I)))))))))))) (TAlphaClass.cab
                              (TAlphaWff.neg
                                (TAlphaWff.neg (nb077SplitAlpha0035 x F I))))))))))))
            (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb077AlphaDummy001 F I) (synWa
                        (synWss (synCsn (synCop (synC0c) I))
                          (Class.cv (nb077AlphaDummy001 F I))) (synWss (synCima (synCpprod
                              (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c))) F)
                            (Class.cv (nb077AlphaDummy001 F I)))
                          (Class.cv (nb077AlphaDummy001 F I)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb077AlphaDummy002 x F I) (synWa
                        (synWss (synCsn (synCop (synC0c) I))
                          (Class.cv (nb077AlphaDummy002 x F I))) (synWss (synCima
                            (synCpprod
                              (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c))) F)
                            (Class.cv (nb077AlphaDummy002 x F I)))
                          (Class.cv (nb077AlphaDummy002 x F I)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
