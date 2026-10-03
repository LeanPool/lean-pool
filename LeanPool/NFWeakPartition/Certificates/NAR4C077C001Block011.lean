/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part031`. -/


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
noncomputable def nb077_split_alpha_0017 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_057 F I))
          (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom
              (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))))
        (Wff.neg (Wff.classMem (Class.cv (nb077_alpha_dummy_057 F I))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_058 x F))
          (syn_ccom (syn_ccnv (syn_c1st))
            (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))))
        (Wff.neg (Wff.classMem (Class.cv (nb077_alpha_dummy_058 x F))
            (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm
                      (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_065 F I) from (by
                          unfold nb077_alpha_dummy_065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0050 F I) 0))))) (Ne.symm
                      (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_066 x) from (by
                          unfold nb077_alpha_dummy_066;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0051 x) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_065 F I) from (by
                            unfold nb077_alpha_dummy_065;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0048 F I) 0))))) (Ne.symm
                        (show (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_066 x) from (by
                            unfold nb077_alpha_dummy_066;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0049 x) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0002 x F I)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_068 F I) from
        (by
          unfold nb077_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080 F I) 1)))) (show (nb077_alpha_dummy_063 x) ≠
        (nb077_alpha_dummy_070 x) from (by
          unfold nb077_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080 F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_097 F I) from (by
          unfold nb077_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084 F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_098 x) from (by
          unfold nb077_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_071 F I) from (by
          unfold nb077_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081 F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_072 x) from (by
          unfold nb077_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0003 x F I))))) (TAlphaWff.classMem
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
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_068 F I) from
        (by
          unfold nb077_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080 F I) 1)))) (show (nb077_alpha_dummy_063 x) ≠
        (nb077_alpha_dummy_070 x) from (by
          unfold nb077_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_067 F I) from (by
          unfold nb077_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0080 F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_069 x) from (by
          unfold nb077_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0082 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_097 F I) from (by
          unfold nb077_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0084 F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_098 x) from (by
          unfold nb077_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0085 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_071 F I) from (by
          unfold nb077_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0081 F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_072 x) from (by
          unfold nb077_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0083 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪
        ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0003 x F I))))) (TAlphaWff.classMem
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
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb077_split_alpha_0004 x F I)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_104 F I) from (by
          unfold nb077_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118 F I)
                  1)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_106 x) from (by
          unfold nb077_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120 x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_103 F I) from (by
          unfold nb077_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118 F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold nb077_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_133 F I) from (by
          unfold nb077_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122 F
                    I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_134 x) from (by
          unfold nb077_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_107 F I) from (by
          unfold nb077_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_108 x) from (by
          unfold nb077_alpha_dummy_108;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0005 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I),
        (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)),
        ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I),
        (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠ (nb077_alpha_dummy_104 F I) from
        (by
          unfold nb077_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118 F I)
                  1)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_106 x) from (by
          unfold nb077_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120 x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_103 F I) from (by
          unfold nb077_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0118 F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_105 x) from (by
          unfold nb077_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0120 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_133 F I) from (by
          unfold nb077_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0122 F
                    I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_134 x) from (by
          unfold nb077_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0123 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_061 F I) ≠
        (nb077_alpha_dummy_107 F I) from (by
          unfold nb077_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0119
                    F I)
                  0)))) (show (nb077_alpha_dummy_064 x) ≠ (nb077_alpha_dummy_108 x) from (by
          unfold nb077_alpha_dummy_108;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0005 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I),
        (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)),
        ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I),
        (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                          (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (Ne.symm (show (nb077_alpha_dummy_140 F I) ≠
                                        (nb077_alpha_dummy_145 F I) from (by
                                        unfold nb077_alpha_dummy_145;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0130 F I) 0))))) (Ne.symm
                                    (show (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_146 x)
                                      from (by
                                        unfold nb077_alpha_dummy_146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0131 x)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb077_alpha_dummy_139 F I) ≠
        (nb077_alpha_dummy_145 F I) from (by
                                          unfold nb077_alpha_dummy_145;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0128 F I) 0))))) (Ne.symm
                                      (show (nb077_alpha_dummy_142 x) ≠
        (nb077_alpha_dummy_146 x) from (by
                                          unfold nb077_alpha_dummy_146;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0129 x) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb077_split_alpha_0006 x F I))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0007 x F I))))) (TAlphaWff.classMem
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
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011
        F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006
        x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_ccompl
        (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_148 F I) from (by
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
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0007 x F I))))) (TAlphaWff.classMem
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
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011
        F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006
        x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_ccompl
        (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.ex
                              (TAlphaWff.neg (nb077_split_alpha_0014 x F I))))))))
                  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb077_split_alpha_0015 x F I)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_312 F I) from (by
          unfold nb077_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336 F I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_314 x) from (by
          unfold nb077_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338 x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_311 F I) from (by
          unfold nb077_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336 F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_313 x) from (by
          unfold nb077_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_341 F I) from (by
          unfold nb077_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340 F
                    I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_342 x) from (by
          unfold nb077_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_315 F I) from (by
          unfold nb077_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_316 x) from (by
          unfold nb077_alpha_dummy_316;
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
        (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv
        (nb077_alpha_dummy_060 F I))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0016 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)), ((nb077_alpha_dummy_312 F I),
        (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
        ((nb077_alpha_dummy_341 F I), (nb077_alpha_dummy_342 x)), ((nb077_alpha_dummy_315 F I),
        (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_312 F I) from
        (by
          unfold nb077_alpha_dummy_312;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336 F I)
                  1)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_314 x) from (by
          unfold nb077_alpha_dummy_314;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338 x)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_311 F I) from (by
          unfold nb077_alpha_dummy_311;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0336 F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_313 x) from (by
          unfold nb077_alpha_dummy_313;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0338 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_341 F I) from (by
          unfold nb077_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0340 F
                    I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_342 x) from (by
          unfold nb077_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0341 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_060 F I) ≠
        (nb077_alpha_dummy_315 F I) from (by
          unfold nb077_alpha_dummy_315;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0337
                    F I)
                  0)))) (show (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_316 x) from (by
          unfold nb077_alpha_dummy_316;
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
        (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv
        (nb077_alpha_dummy_060 F I))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb077_split_alpha_0016 x F I))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_343 F I), (nb077_alpha_dummy_344 x)), ((nb077_alpha_dummy_312 F I),
        (nb077_alpha_dummy_314 x)), ((nb077_alpha_dummy_311 F I), (nb077_alpha_dummy_313 x)),
        ((nb077_alpha_dummy_341 F I), (nb077_alpha_dummy_342 x)), ((nb077_alpha_dummy_315 F I),
        (nb077_alpha_dummy_316 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
        (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_ccompl (syn_csn (syn_c0c))) (by
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
                        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                      (syn_ccnv (syn_c1st)) (nb077_wpp_refl_0062 x F I)))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn
          [((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
            ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
            ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
          (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))
          (nb077_wpp_refl_0063 x F I)))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part032`. -/


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
noncomputable def nb077_split_alpha_0018 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.classMem (Class.cv (nb077_alpha_dummy_023 F I)) (syn_ccompl
          (Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))))
      (Wff.classMem (Class.cv (nb077_alpha_dummy_024 x F I)) (syn_ccompl
          (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_018 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_020 F I) from (by
                            unfold nb077_alpha_dummy_020;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0010 F I) 1)))) (show
                          (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_022 x F I) from (by
                            unfold nb077_alpha_dummy_022;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_019 F I) from
                            (by
                              unfold nb077_alpha_dummy_019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0010 F I) 0)))) (show
                            (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_021 x F I) from
                            (by
                              unfold nb077_alpha_dummy_021;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_025 F I) from (by
                                unfold nb077_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0014 F I) 0)))) (show
                              (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_026 x F I) from
                              (by
                                unfold nb077_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0015 x F I)
                                        0)))) (TAlphaVar.there (show
                                (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_023 F I) from
                                (by
                                  unfold nb077_alpha_dummy_023;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0011 F I)
                                          0)))) (show (nb077_alpha_dummy_018 x F I) ≠
                                  (nb077_alpha_dummy_024 x F I) from (by
                                  unfold nb077_alpha_dummy_024;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0013 x F I)
                                          0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
                            ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
                            ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_020 F I) ≠
                                    (nb077_alpha_dummy_027 F I) from (by
                                    unfold nb077_alpha_dummy_027;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                            0)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                    (nb077_alpha_dummy_029 x F I) from (by
                                    unfold nb077_alpha_dummy_029;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                            0)))) (TAlphaVar.there (show
                                    (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_028 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_028;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                              1)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                      (nb077_alpha_dummy_030 x F I) from (by
                                      unfold nb077_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0017 x F I) 1))))
                                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_034 F I) from (by
          unfold nb077_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  1)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_037 x F I) from
        (by
          unfold nb077_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_033 F I) from (by
          unfold nb077_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F
                    I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_036 x F I) from
        (by
          unfold nb077_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x
                    F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018
                    F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_032 x F I) from
        (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_045 F I) from (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_045 F I) from
        (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_031 F I),
        (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I),
        (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I),
        (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_020 F I),
        (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I),
        (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_025 F I),
        (nb077_alpha_dummy_026 x F I)), ((nb077_alpha_dummy_023 F I),
        (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_031 F I),
        (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I),
        (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I),
        (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_020 F I),
        (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I),
        (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_025 F I),
        (nb077_alpha_dummy_026 x F I)), ((nb077_alpha_dummy_023 F I),
        (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_020 F I) from (by
                            unfold nb077_alpha_dummy_020;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0010 F I) 1)))) (show
                          (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_022 x F I) from (by
                            unfold nb077_alpha_dummy_022;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_019 F I) from
                            (by
                              unfold nb077_alpha_dummy_019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0010 F I) 0)))) (show
                            (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_021 x F I) from
                            (by
                              unfold nb077_alpha_dummy_021;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_025 F I) from (by
                                unfold nb077_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0014 F I) 0)))) (show
                              (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_026 x F I) from
                              (by
                                unfold nb077_alpha_dummy_026;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0015 x F I)
                                        0)))) (TAlphaVar.there (show
                                (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_023 F I) from
                                (by
                                  unfold nb077_alpha_dummy_023;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0011 F I)
                                          0)))) (show (nb077_alpha_dummy_018 x F I) ≠
                                  (nb077_alpha_dummy_024 x F I) from (by
                                  unfold nb077_alpha_dummy_024;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0013 x F I)
                                          0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
                            ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
                            ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_020 F I) ≠
                                    (nb077_alpha_dummy_027 F I) from (by
                                    unfold nb077_alpha_dummy_027;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                            0)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                    (nb077_alpha_dummy_029 x F I) from (by
                                    unfold nb077_alpha_dummy_029;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                            0)))) (TAlphaVar.there (show
                                    (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_028 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_028;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                              1)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                      (nb077_alpha_dummy_030 x F I) from (by
                                      unfold nb077_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0017 x F I) 1))))
                                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_034 F I) from (by
          unfold nb077_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  1)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_037 x F I) from
        (by
          unfold nb077_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_033 F I) from (by
          unfold nb077_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F
                    I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_036 x F I) from
        (by
          unfold nb077_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x
                    F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018
                    F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_032 x F I) from
        (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_045 F I) from (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_045 F I) from
        (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_031 F I),
        (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I),
        (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I),
        (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_020 F I),
        (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I),
        (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_025 F I),
        (nb077_alpha_dummy_026 x F I)), ((nb077_alpha_dummy_023 F I),
        (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_031 F I),
        (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I),
        (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I),
        (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_020 F I),
        (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I),
        (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_025 F I),
        (nb077_alpha_dummy_026 x F I)), ((nb077_alpha_dummy_023 F I),
        (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part033`. -/


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
noncomputable def nb077_split_alpha_0019 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
        (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c))))
      (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
        (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
            ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (by decide)) (freshVar_injective
          (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
            ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_020 F I) ≠
                                    (nb077_alpha_dummy_027 F I) from (by
                                    unfold nb077_alpha_dummy_027;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                            0)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                    (nb077_alpha_dummy_029 x F I) from (by
                                    unfold nb077_alpha_dummy_029;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                            0)))) (TAlphaVar.there (show
                                    (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_028 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_028;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                              1)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                      (nb077_alpha_dummy_030 x F I) from (by
                                      unfold nb077_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0017 x F I) 1))))
                                  (TAlphaVar.there (show (nb077_alpha_dummy_020 F I) ≠
                                        (nb077_alpha_dummy_053 F I) from (by
                                        unfold nb077_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0046 F I) 0)))) (show
                                      (nb077_alpha_dummy_022 x F I) ≠
                                        (nb077_alpha_dummy_054 x F I) from (by
                                        unfold nb077_alpha_dummy_054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0047 x F I) 0))))
                                    (TAlphaVar.there (show (nb077_alpha_dummy_020 F I) ≠
        (nb077_alpha_dummy_051 F I) from (by
                                          unfold nb077_alpha_dummy_051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0044 F I) 0)))) (show
                                        (nb077_alpha_dummy_022 x F I) ≠
        (nb077_alpha_dummy_052 x F I) from (by
                                          unfold nb077_alpha_dummy_052;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0045 x F I) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_034 F I) from (by
          unfold nb077_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  1)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_037 x F I) from
        (by
          unfold nb077_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_033 F I) from (by
          unfold nb077_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F
                    I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_036 x F I) from
        (by
          unfold nb077_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x
                    F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018
                    F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_032 x F I) from
        (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)),
        ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)),
        ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_045 F I) from (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_045 F I) from
        (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_031 F I),
        (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I),
        (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I),
        (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I),
        (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I),
        (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I),
        (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I),
        (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I),
        (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I),
        (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_031 F I),
        (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I),
        (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I),
        (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I),
        (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I),
        (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I),
        (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I),
        (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I),
        (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I),
        (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_020 F I) ≠
                                    (nb077_alpha_dummy_027 F I) from (by
                                    unfold nb077_alpha_dummy_027;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                            0)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                    (nb077_alpha_dummy_029 x F I) from (by
                                    unfold nb077_alpha_dummy_029;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                            0)))) (TAlphaVar.there (show
                                    (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_028 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_028;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                              1)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                      (nb077_alpha_dummy_030 x F I) from (by
                                      unfold nb077_alpha_dummy_030;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0017 x F I) 1))))
                                  (TAlphaVar.there (show (nb077_alpha_dummy_020 F I) ≠
                                        (nb077_alpha_dummy_053 F I) from (by
                                        unfold nb077_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0046 F I) 0)))) (show
                                      (nb077_alpha_dummy_022 x F I) ≠
                                        (nb077_alpha_dummy_054 x F I) from (by
                                        unfold nb077_alpha_dummy_054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0047 x F I) 0))))
                                    (TAlphaVar.there (show (nb077_alpha_dummy_020 F I) ≠
        (nb077_alpha_dummy_051 F I) from (by
                                          unfold nb077_alpha_dummy_051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0044 F I) 0)))) (show
                                        (nb077_alpha_dummy_022 x F I) ≠
        (nb077_alpha_dummy_052 x F I) from (by
                                          unfold nb077_alpha_dummy_052;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0045 x F I) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_034 F I) from (by
          unfold nb077_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  1)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_037 x F I) from
        (by
          unfold nb077_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F
                    I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_033 F I) from (by
          unfold nb077_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F
                    I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_036 x F I) from
        (by
          unfold nb077_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x
                    F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018
                    F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_032 x F I) from
        (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)),
        ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)),
        ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_045 F I) from (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_045 F I) from
        (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x
                    F
                    I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F
                    I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F
                    I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x
                    F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_031 F I),
        (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I),
        (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I),
        (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I),
        (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I),
        (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I),
        (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I),
        (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I),
        (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I),
        (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I) 0)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_031 F I),
        (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I),
        (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I),
        (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_053 F I),
        (nb077_alpha_dummy_054 x F I)), ((nb077_alpha_dummy_051 F I),
        (nb077_alpha_dummy_052 x F I)), ((nb077_alpha_dummy_020 F I),
        (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I),
        (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_049 F I),
        (nb077_alpha_dummy_050 x F I)), ((nb077_alpha_dummy_023 F I),
        (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.refl_of_closed
              [((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
                ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
                ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
                ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
                ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
                ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
              (syn_ccompl (syn_csn (syn_c0c)))
              (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
