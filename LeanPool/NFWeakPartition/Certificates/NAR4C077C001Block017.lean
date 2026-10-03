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

@[expose]
noncomputable def nb077_split_alpha_0035 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_055 F I)) (syn_cnin
            (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
                (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_055 F I)) (syn_cnin
              (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
                  (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))
              (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_056 x F)) (syn_cnin
            (syn_ccom (syn_ccnv (syn_c1st))
              (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_056 x F)) (syn_cnin
              (syn_ccom (syn_ccnv (syn_c1st))
                (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))
              (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (Ne.symm (show
                                (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_065 F I) from
                                (by
                                  unfold nb077_alpha_dummy_065;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0050 F I)
                                          0))))) (Ne.symm
                              (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_066 x) from
                                (by
                                  unfold nb077_alpha_dummy_066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0051 x) 0)))))
                            (TAlphaVar.there (Ne.symm (show (nb077_alpha_dummy_059 F I) ≠
                                    (nb077_alpha_dummy_065 F I) from (by
                                    unfold nb077_alpha_dummy_065;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0048 F I)
                                            0))))) (Ne.symm (show
                                  (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_066 x) from (by
                                    unfold nb077_alpha_dummy_066;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0049 x)
                                            0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb077_split_alpha_0020 x F I)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_068 F I) from (by
          unfold nb077_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080 F
                    I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_070 x) from (by
          unfold nb077_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082 x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_097 F I) from (by
          unfold nb077_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_098 x) from (by
          unfold nb077_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_071 F I) from (by
          unfold
            nb077_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_072 x) from (by
          unfold
            nb077_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0021 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)), ((nb077_alpha_dummy_068 F I),
        (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
        ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)), ((nb077_alpha_dummy_071 F I),
        (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_068 F I) from
        (by
          unfold nb077_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080 F
                    I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_070 x) from (by
          unfold nb077_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082 x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_097 F I) from (by
          unfold nb077_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_098 x) from (by
          unfold nb077_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_071 F I) from (by
          unfold
            nb077_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_072 x) from (by
          unfold
            nb077_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0021 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)), ((nb077_alpha_dummy_068 F I),
        (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
        ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)), ((nb077_alpha_dummy_071 F I),
        (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb077_split_alpha_0022 x F I)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
          unfold nb077_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  1)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_106 x) from (by
          unfold nb077_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_103 F I) from (by
          unfold
            nb077_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold
            nb077_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_133 F I) from (by
          unfold
            nb077_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_134 x) from (by
          unfold
            nb077_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_107 F I) from (by
          unfold
            nb077_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_108 x) from (by
          unfold
            nb077_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0121
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0023 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I),
        (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)),
        ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I),
        (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F
        I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x
        F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F
        I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
          unfold nb077_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  1)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_106 x) from (by
          unfold nb077_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_103 F I) from (by
          unfold
            nb077_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold
            nb077_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_133 F I) from (by
          unfold
            nb077_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_134 x) from (by
          unfold
            nb077_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_107 F I) from (by
          unfold
            nb077_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_108 x) from (by
          unfold
            nb077_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0121
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0023 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I),
        (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)),
        ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I),
        (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F
        I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x
        F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F
        I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (Ne.symm (show
        (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_145 F I) from (by
          unfold nb077_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0130 F I)
                  0))))) (Ne.symm (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_146 x)
        from (by
          unfold nb077_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0131 x) 0))))) (TAlphaVar.there (Ne.symm (show
        (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_145 F I) from (by
          unfold nb077_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0128 F I)
                  0))))) (Ne.symm (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_146 x)
        from (by
          unfold nb077_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0129 x)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0024 x F I)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_148 F I) from
        (by
          unfold
            nb077_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  1)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_150 x) from (by
          unfold
            nb077_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_147 F I) from (by
          unfold
            nb077_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_149 x) from (by
          unfold
            nb077_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_177 F I) from (by
          unfold
            nb077_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0164
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_178 x) from (by
          unfold
            nb077_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0165
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_151 F I) from (by
          unfold
            nb077_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0161
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_152 x) from (by
          unfold
            nb077_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0163
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0025 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)), ((nb077_alpha_dummy_148 F I),
        (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
        ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)), ((nb077_alpha_dummy_151 F I),
        (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055
        F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018
        x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004
        F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_140
        F I) ≠ (nb077_alpha_dummy_148 F I) from (by
          unfold
            nb077_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  1)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_150 x) from (by
          unfold
            nb077_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_147 F I) from (by
          unfold
            nb077_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_149 x) from (by
          unfold
            nb077_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_177 F I) from (by
          unfold
            nb077_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0164
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_178 x) from (by
          unfold
            nb077_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0165
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_151 F I) from (by
          unfold
            nb077_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0161
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_152 x) from (by
          unfold
            nb077_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0163
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0025 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)), ((nb077_alpha_dummy_148 F I),
        (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
        ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)), ((nb077_alpha_dummy_151 F I),
        (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055
        F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018
        x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004
        F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex
                                      (TAlphaWff.neg (nb077_split_alpha_0032 x F I))))))))
                          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.neg (nb077_split_alpha_0033 x F I)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_312 F I) from (by
          unfold nb077_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_314 x) from (by
          unfold nb077_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_311 F I) from (by
          unfold
            nb077_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_313 x) from (by
          unfold
            nb077_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_341 F I) from (by
          unfold
            nb077_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_342 x) from (by
          unfold
            nb077_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_315 F I) from (by
          unfold
            nb077_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_316 x) from (by
          unfold
            nb077_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0339
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv
        (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) (by decide))
        (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv)
        (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F
        I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0034 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_343 F I),
        (nb077_alpha_dummy_344 x)), ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
        ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_341 F I),
        (nb077_alpha_dummy_342 x)), ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x
        F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F
        I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x
        F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_312 F I) from (by
          unfold nb077_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_314 x) from (by
          unfold nb077_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_311 F I) from (by
          unfold
            nb077_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_313 x) from (by
          unfold
            nb077_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_341 F I) from (by
          unfold
            nb077_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_342 x) from (by
          unfold
            nb077_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_315 F I) from (by
          unfold
            nb077_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_316 x) from (by
          unfold
            nb077_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0339
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv
        (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) (by decide))
        (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv)
        (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F
        I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0034 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_343 F I),
        (nb077_alpha_dummy_344 x)), ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
        ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_341 F I),
        (nb077_alpha_dummy_342 x)), ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x
        F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F
        I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x
        F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                              [((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                                ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                                ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                                ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                                ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                                ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                              (syn_ccnv (syn_c1st)) (nb077_wpp_refl_0124 x F I))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_reflOn
                [((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                  ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                  ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                  ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                  ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                  ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                  ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))
                (nb077_wpp_refl_0125 x F I))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                            (TAlphaVar.there (Ne.symm (show (nb077_alpha_dummy_060 F I) ≠
                                    (nb077_alpha_dummy_065 F I) from (by
                                    unfold nb077_alpha_dummy_065;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0050 F I)
                                            0))))) (Ne.symm (show
                                  (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_066 x) from (by
                                    unfold nb077_alpha_dummy_066;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0051 x)
                                            0))))) (TAlphaVar.there (Ne.symm (show
                                    (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_065 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_065;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0048 F I)
                                              0))))) (Ne.symm (show
                                    (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_066 x) from
                                    (by
                                      unfold nb077_alpha_dummy_066;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0049 x)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb077_split_alpha_0020 x F I)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_068 F I) from
        (by
          unfold nb077_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_070 x) from (by
          unfold nb077_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_097 F I) from (by
          unfold
            nb077_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_098 x) from (by
          unfold
            nb077_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_071 F I) from (by
          unfold
            nb077_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_072 x) from (by
          unfold
            nb077_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0021 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)), ((nb077_alpha_dummy_068 F I),
        (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
        ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)), ((nb077_alpha_dummy_071 F I),
        (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F
        I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F
        I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_ccompl
        (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_068 F I) from (by
          unfold nb077_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_070 x) from (by
          unfold nb077_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_097 F I) from (by
          unfold
            nb077_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_098 x) from (by
          unfold
            nb077_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_071 F I) from (by
          unfold
            nb077_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_072 x) from (by
          unfold
            nb077_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0021 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_099 F I), (nb077_alpha_dummy_100 x)), ((nb077_alpha_dummy_068 F I),
        (nb077_alpha_dummy_070 x)), ((nb077_alpha_dummy_067 F I), (nb077_alpha_dummy_069 x)),
        ((nb077_alpha_dummy_097 F I), (nb077_alpha_dummy_098 x)), ((nb077_alpha_dummy_071 F I),
        (nb077_alpha_dummy_072 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F
        I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F
        I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_ccompl
        (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0022 x F I))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_104 F I) from
        (by
          unfold
            nb077_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  1)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_106 x) from (by
          unfold
            nb077_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_103 F I) from (by
          unfold
            nb077_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold
            nb077_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_133 F I) from (by
          unfold
            nb077_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_134 x) from (by
          unfold
            nb077_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_107 F I) from (by
          unfold
            nb077_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_108 x) from (by
          unfold
            nb077_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0121
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0023 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I),
        (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)),
        ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I),
        (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055
        F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018
        x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004
        F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
          unfold
            nb077_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  1)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_106 x) from (by
          unfold
            nb077_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_103 F I) from (by
          unfold
            nb077_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold
            nb077_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_133 F I) from (by
          unfold
            nb077_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_134 x) from (by
          unfold
            nb077_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_107 F I) from (by
          unfold
            nb077_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_108 x) from (by
          unfold
            nb077_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0121
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_061 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0023 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I),
        (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)),
        ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I),
        (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055
        F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018
        x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004
        F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (Ne.symm (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_145 F I) from (by
          unfold nb077_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0130 F I)
                  0))))) (Ne.symm (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_146 x)
        from (by
          unfold nb077_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0131 x)
                  0))))) (TAlphaVar.there (Ne.symm (show (nb077_alpha_dummy_139 F I) ≠
        (nb077_alpha_dummy_145 F I) from (by
          unfold nb077_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0128 F I)
                  0))))) (Ne.symm (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_146 x)
        from (by
          unfold nb077_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0129 x)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0024 x F I)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_148 F I) from
        (by
          unfold
            nb077_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  1)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_150 x) from (by
          unfold
            nb077_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_147 F I) from (by
          unfold
            nb077_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_149 x) from (by
          unfold
            nb077_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_177 F I) from (by
          unfold
            nb077_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0164
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_178 x) from (by
          unfold
            nb077_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0165
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_151 F I) from (by
          unfold
            nb077_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0161
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_152 x) from (by
          unfold
            nb077_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0163
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0025 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)), ((nb077_alpha_dummy_148 F I),
        (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
        ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)), ((nb077_alpha_dummy_151 F I),
        (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055
        F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018
        x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004
        F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_140
        F I) ≠ (nb077_alpha_dummy_148 F I) from (by
          unfold
            nb077_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  1)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_150 x) from (by
          unfold
            nb077_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_147 F I) from (by
          unfold
            nb077_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0160
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_149 x) from (by
          unfold
            nb077_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0162
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_177 F I) from (by
          unfold
            nb077_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0164
                    F I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_178 x) from (by
          unfold
            nb077_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0165
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_140 F I) ≠
        (nb077_alpha_dummy_151 F I) from (by
          unfold
            nb077_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0161
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_152 x) from (by
          unfold
            nb077_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0163
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0025 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)), ((nb077_alpha_dummy_148 F I),
        (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
        ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)), ((nb077_alpha_dummy_151 F I),
        (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055
        F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018
        x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004
        F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex (TAlphaWff.neg
        (nb077_split_alpha_0032 x F I)))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0033 x F I))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_312 F I) from
        (by
          unfold
            nb077_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_314 x) from (by
          unfold
            nb077_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_311 F I) from (by
          unfold
            nb077_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_313 x) from (by
          unfold
            nb077_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_341 F I) from (by
          unfold
            nb077_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_342 x) from (by
          unfold
            nb077_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_315 F I) from (by
          unfold
            nb077_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_316 x) from (by
          unfold
            nb077_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0339
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv
        (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) (by decide))
        (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv)
        (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F
        I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0034 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_343 F I),
        (nb077_alpha_dummy_344 x)), ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
        ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_341 F I),
        (nb077_alpha_dummy_342 x)), ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056
        x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001
        F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005
        x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_312 F I) from (by
          unfold
            nb077_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_314 x) from (by
          unfold
            nb077_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_311 F I) from (by
          unfold
            nb077_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_313 x) from (by
          unfold
            nb077_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_341 F I) from (by
          unfold
            nb077_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_342 x) from (by
          unfold
            nb077_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_315 F I) from (by
          unfold
            nb077_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_316 x) from (by
          unfold
            nb077_alpha_dummy_316;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0339
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪
        ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv
        (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) (by decide))
        (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv)
        (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F
        I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪
        ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0034 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_343 F I),
        (nb077_alpha_dummy_344 x)), ((nb077_alpha_dummy_312 F I), (nb077_alpha_dummy_314 x)),
        ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)), ((nb077_alpha_dummy_341 F I),
        (nb077_alpha_dummy_342 x)), ((nb077_alpha_dummy_315 F I), (nb077_alpha_dummy_316 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056
        x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001
        F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005
        x F I))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                [((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                  ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                  ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                  ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                  ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                                  ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                  ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                                  ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                                  ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                                  ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                                  ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                                (syn_ccnv (syn_c1st)) (nb077_wpp_refl_0124 x F I))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_reflOn
                  [((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                    ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                    ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                    ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                    ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                    ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                  (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))
                  (nb077_wpp_refl_0125 x F I)))))))))

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

@[expose]
noncomputable def nominal_df_frec (x : Var) (F : Class) (I : Class) (__dv_F_x : x ∉ F.fv)
    (__dv_I_x : x ∉ I.fv) :
    Nominal.NPrf
      (.classEq (syn_cfrec F I) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
          (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F))) :=
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
                                    (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_009 F I),
        (nb077_alpha_dummy_010 x F I)), ((nb077_alpha_dummy_007 F I),
        (nb077_alpha_dummy_008 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_csn (syn_cop (syn_c0c) I))
                                      (nb077_wpp_refl_0000 x F I))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_009 F I) from (by
          unfold nb077_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0002 F I) 0)))) (show (nb077_alpha_dummy_002 x F I) ≠
        (nb077_alpha_dummy_010 x F I) from (by
          unfold nb077_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0003 x F I) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_001 F I) ≠ (nb077_alpha_dummy_007 F I) from (by
          unfold nb077_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0000 F I) 0)))) (show (nb077_alpha_dummy_002 x F I) ≠
        (nb077_alpha_dummy_008 x F I) from (by
          unfold nb077_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0001 x F I) 0)))) (TAlphaVar.here _ _ _)))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_009 F I),
        (nb077_alpha_dummy_010 x F I)), ((nb077_alpha_dummy_007 F I),
        (nb077_alpha_dummy_008 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_csn (syn_cop (syn_c0c) I))
                                      (nb077_wpp_refl_0000 x F I))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_009 F I) from (by
          unfold nb077_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0002 F I) 0)))) (show (nb077_alpha_dummy_002 x F I) ≠
        (nb077_alpha_dummy_010 x F I) from (by
          unfold nb077_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0003 x F I) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_001 F I) ≠ (nb077_alpha_dummy_007 F I) from (by
          unfold nb077_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0000 F I) 0)))) (show (nb077_alpha_dummy_002 x F I) ≠
        (nb077_alpha_dummy_008 x F I) from (by
          unfold nb077_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0001 x F I) 0)))) (TAlphaVar.here _ _ _))))))))))))
                    (TAlphaClass.refl_of_reflOn
                      [((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                      (syn_csn (syn_cop (syn_c0c) I)) (nb077_wpp_refl_0001 x F I)))
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_001 F I) ≠ (nb077_alpha_dummy_016 F I) from (by
          unfold nb077_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0008 F I)
                  1)))) (show (nb077_alpha_dummy_002 x F I) ≠ (nb077_alpha_dummy_018 x F I) from
        (by
          unfold nb077_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0009 x F I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_015 F I) from (by
          unfold nb077_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0008 F I)
                  0)))) (show (nb077_alpha_dummy_002 x F I) ≠ (nb077_alpha_dummy_017 x F I) from
        (by
          unfold nb077_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0009 x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_013 F I) from (by
          unfold nb077_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0006 F
                    I)
                  0)))) (show (nb077_alpha_dummy_002 x F I) ≠ (nb077_alpha_dummy_014 x F I) from
        (by
          unfold nb077_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0007 x
                    F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_011 F I) from (by
          unfold nb077_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0004
                    F I)
                  0)))) (show (nb077_alpha_dummy_002 x F I) ≠ (nb077_alpha_dummy_012 x F I) from
        (by
          unfold nb077_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0005
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0000 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_020 F I) from (by
          unfold
            nb077_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_022 x F I) from
        (by
          unfold
            nb077_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_019 F I) from (by
          unfold
            nb077_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_021 x F I) from
        (by
          unfold
            nb077_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_049 F I) from (by
          unfold
            nb077_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_050 x F I) from
        (by
          unfold
            nb077_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_023 F I) from (by
          unfold
            nb077_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_024 x F I) from
        (by
          unfold
            nb077_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_cpprod (syn_cmpt
        (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
        (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) (by
          decide)) (freshVar_injective (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv
        x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F
        I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.neg (nb077_split_alpha_0001 x F I))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_020 F I) from
        (by
          unfold
            nb077_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_022 x F I) from
        (by
          unfold
            nb077_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_019 F I) from (by
          unfold
            nb077_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_021 x F I) from
        (by
          unfold
            nb077_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_049 F I) from (by
          unfold
            nb077_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_050 x F I) from
        (by
          unfold
            nb077_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_023 F I) from (by
          unfold
            nb077_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_024 x F I) from
        (by
          unfold
            nb077_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_cpprod (syn_cmpt
        (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
        (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) (by
          decide)) (freshVar_injective (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv
        x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F
        I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.neg (nb077_split_alpha_0001 x F I)))))))))))))))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0017 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0017 x F I))))))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_013 F I) from (by
          unfold nb077_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0006 F I) 0)))) (show (nb077_alpha_dummy_002 x F I) ≠
        (nb077_alpha_dummy_014 x F I) from (by
          unfold nb077_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0007 x F I) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_001 F I) ≠ (nb077_alpha_dummy_011 F I) from (by
          unfold nb077_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0004 F I) 0)))) (show (nb077_alpha_dummy_002 x F I) ≠
        (nb077_alpha_dummy_012 x F I) from (by
          unfold nb077_alpha_dummy_012;
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
        (nb077_alpha_dummy_001 F I) ≠ (nb077_alpha_dummy_016 F I) from (by
          unfold nb077_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0008 F I)
                  1)))) (show (nb077_alpha_dummy_002 x F I) ≠ (nb077_alpha_dummy_018 x F I) from
        (by
          unfold nb077_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0009 x F I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_015 F I) from (by
          unfold nb077_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0008 F I)
                  0)))) (show (nb077_alpha_dummy_002 x F I) ≠ (nb077_alpha_dummy_017 x F I) from
        (by
          unfold nb077_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0009 x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_013 F I) from (by
          unfold nb077_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0006 F
                    I)
                  0)))) (show (nb077_alpha_dummy_002 x F I) ≠ (nb077_alpha_dummy_014 x F I) from
        (by
          unfold nb077_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0007 x
                    F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_011 F I) from (by
          unfold nb077_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0004
                    F I)
                  0)))) (show (nb077_alpha_dummy_002 x F I) ≠ (nb077_alpha_dummy_012 x F I) from
        (by
          unfold nb077_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0005
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0000 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_020 F I) from (by
          unfold
            nb077_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_022 x F I) from
        (by
          unfold
            nb077_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_019 F I) from (by
          unfold
            nb077_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_021 x F I) from
        (by
          unfold
            nb077_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_049 F I) from (by
          unfold
            nb077_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_050 x F I) from
        (by
          unfold
            nb077_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_023 F I) from (by
          unfold
            nb077_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_024 x F I) from
        (by
          unfold
            nb077_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_cpprod (syn_cmpt
        (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
        (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) (by
          decide)) (freshVar_injective (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv
        x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F
        I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.neg (nb077_split_alpha_0001 x F I))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_020 F I) from
        (by
          unfold
            nb077_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_022 x F I) from
        (by
          unfold
            nb077_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_019 F I) from (by
          unfold
            nb077_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_021 x F I) from
        (by
          unfold
            nb077_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_049 F I) from (by
          unfold
            nb077_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_050 x F I) from
        (by
          unfold
            nb077_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_023 F I) from (by
          unfold
            nb077_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_024 x F I) from
        (by
          unfold
            nb077_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_cpprod (syn_cmpt
        (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
        (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) (by
          decide)) (freshVar_injective (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv
        x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F
        I))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.neg (nb077_split_alpha_0001 x F I)))))))))))))))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0017 x F I))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0017 x F I))))))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
        (nb077_alpha_dummy_013 F I) from (by
          unfold nb077_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0006 F I) 0)))) (show (nb077_alpha_dummy_002 x F I) ≠
        (nb077_alpha_dummy_014 x F I) from (by
          unfold nb077_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0007 x F I) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_001 F I) ≠ (nb077_alpha_dummy_011 F I) from (by
          unfold nb077_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0004 F I) 0)))) (show (nb077_alpha_dummy_002 x F I) ≠
        (nb077_alpha_dummy_012 x F I) from (by
          unfold nb077_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0005 x F I) 0)))) (TAlphaVar.here _ _ _))))))))))))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_001 F I) ≠
                                    (nb077_alpha_dummy_016 F I) from (by
                                    unfold nb077_alpha_dummy_016;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0008 F I)
                                            1)))) (show (nb077_alpha_dummy_002 x F I) ≠
                                    (nb077_alpha_dummy_018 x F I) from (by
                                    unfold nb077_alpha_dummy_018;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0009 x F I)
                                            1)))) (TAlphaVar.there (show
                                    (nb077_alpha_dummy_001 F I) ≠ (nb077_alpha_dummy_015 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_015;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0008 F I)
                                              0)))) (show (nb077_alpha_dummy_002 x F I) ≠
                                      (nb077_alpha_dummy_017 x F I) from (by
                                      unfold nb077_alpha_dummy_017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0009 x F I) 0))))
                                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (nb077_split_alpha_0018 x F I)
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_020 F I) from (by
          unfold nb077_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_022 x F I) from
        (by
          unfold nb077_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_019 F I) from (by
          unfold
            nb077_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_021 x F I) from
        (by
          unfold
            nb077_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_049 F I) from (by
          unfold
            nb077_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_050 x F I) from
        (by
          unfold
            nb077_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_023 F I) from (by
          unfold
            nb077_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_024 x F I) from
        (by
          unfold
            nb077_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_cpprod (syn_cmpt
        (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
        (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) (by decide))
        (freshVar_injective (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x)
        (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb077_split_alpha_0019 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_020 F I) from
        (by
          unfold nb077_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  1)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_022 x F I) from
        (by
          unfold nb077_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_019 F I) from (by
          unfold
            nb077_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0038
                    F I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_021 x F I) from
        (by
          unfold
            nb077_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0040
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_049 F I) from (by
          unfold
            nb077_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0042
                    F I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_050 x F I) from
        (by
          unfold
            nb077_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0043
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_015 F I) ≠
        (nb077_alpha_dummy_023 F I) from (by
          unfold
            nb077_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0039
                    F I)
                  0)))) (show (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_024 x F I) from
        (by
          unfold
            nb077_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0041
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_cpprod (syn_cmpt
        (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
        (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) (by decide))
        (freshVar_injective (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x)
        (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb077_split_alpha_0019 x F I)))))))))))) (TAlphaClass.cab
                              (TAlphaWff.neg
                                (TAlphaWff.neg (nb077_split_alpha_0035 x F I))))))))))))
            (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa
                        (syn_wss (syn_csn (syn_cop (syn_c0c) I))
                          (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod
                              (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)
                            (Class.cv (nb077_alpha_dummy_001 F I)))
                          (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa
                        (syn_wss (syn_csn (syn_cop (syn_c0c) I))
                          (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima
                            (syn_cpprod
                              (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)
                            (Class.cv (nb077_alpha_dummy_002 x F I)))
                          (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
