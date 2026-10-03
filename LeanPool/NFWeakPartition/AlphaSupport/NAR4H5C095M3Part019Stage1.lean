/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part018

/-! NF weak partition development: NAR4H5C095M3Part019. -/


public section


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
noncomputable def nb095_split_alpha_0029 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (syn_wfun (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (Wff.neg
          (Wff.classEq (syn_cdm (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))))
      (Wff.imp (syn_wfun (Class.cv f)) (Wff.neg (Wff.classEq (syn_cdm (Class.cv f)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
                              (nb095_split_alpha_0010 x u D R S_cls f E dv_f_u dv_f_x))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn
                        [((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
                          ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)]
                        (syn_cid) (nb095_wpp_refl_0035 x u D R S_cls f E)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
                              (nb095_split_alpha_0010 x u D R S_cls f E dv_f_u dv_f_x))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn
                        [((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
                          ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)]
                        (syn_cid) (nb095_wpp_refl_0035 x u D R S_cls f E))))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                        (nb095_alpha_dummy_012 D R S_cls E) ≠
                          (nb095_alpha_dummy_017 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0002 D R S_cls E)
                                  0))))) (Ne.symm
                      (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_018 f) from (by
                          unfold nb095_alpha_dummy_018;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0003 f) 0)))))
                    (TAlphaVar.there (Ne.symm (show (nb095_alpha_dummy_011 D R S_cls E) ≠
                            (nb095_alpha_dummy_017 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_017;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0000 D R S_cls E)
                                    0))))) (Ne.symm
                        (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_018 f) from (by
                            unfold nb095_alpha_dummy_018;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0001 f) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb095_split_alpha_0011 x u D R S_cls f E)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb095_split_alpha_0012 x u D R S_cls f E)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb095_split_alpha_0012 x u D R S_cls f E)))))))))))))
              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                  (nb095_split_alpha_0013 x u D R S_cls f E)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_056 D R S_cls E) from (by
          unfold nb095_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_058 f) from (by
          unfold nb095_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
        (nb095_alpha_dummy_055 D R S_cls E) from (by
          unfold nb095_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_057 f) from (by
          unfold nb095_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
        (nb095_alpha_dummy_085 D R S_cls E) from (by
          unfold nb095_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0074 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_086 f) from (by
          unfold nb095_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0075 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
        (nb095_alpha_dummy_059 D R S_cls E) from (by
          unfold nb095_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0071
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_060 f) from (by
          unfold nb095_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0073
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_011 D R S_cls
        E))).fv ∪ ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_016 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095_split_alpha_0014 x u D R S_cls f E))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_056 D R S_cls E) from (by
          unfold nb095_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_058 f) from (by
          unfold nb095_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
        (nb095_alpha_dummy_055 D R S_cls E) from (by
          unfold nb095_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_057 f) from (by
          unfold nb095_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
        (nb095_alpha_dummy_085 D R S_cls E) from (by
          unfold nb095_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0074 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_086 f) from (by
          unfold nb095_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0075 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
        (nb095_alpha_dummy_059 D R S_cls E) from (by
          unfold nb095_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0071
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_060 f) from (by
          unfold nb095_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0073
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_011 D R S_cls
        E))).fv ∪ ((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_016 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095_split_alpha_0014 x u D R S_cls f E)))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                                (TAlphaVar.there (Ne.symm (show
                                      (nb095_alpha_dummy_092 D R S_cls E) ≠
                                        (nb095_alpha_dummy_095 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_095;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0082 D R S_cls E)
                                                0))))) (Ne.symm (show
                                      (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_096 f) from
                                      (by
                                        unfold nb095_alpha_dummy_096;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0083 f)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_095 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0080 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_096 f)
                                        from (by
                                          unfold nb095_alpha_dummy_096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0081 f) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0015 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold
            nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold
            nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold
            nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold
            nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091 D
        R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0016 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_129 D
        R S_cls E), (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099
        f)), ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold
            nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold
            nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold
            nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold
            nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091 D
        R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0016 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_129 D
        R S_cls E), (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099
        f)), ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0017 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold
            nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold
            nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold
            nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold
            nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0018 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold
            nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold
            nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold
            nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold
            nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0018 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_000 D R S_cls E) ≠
                                      (nb095_alpha_dummy_092 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0170 D R S_cls E) 1))))
                                  (show f ≠ (nb095_alpha_dummy_094 f) from (by
                                      unfold nb095_alpha_dummy_094;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0171 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_000 D R S_cls E) ≠
                                        (nb095_alpha_dummy_091 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0170 D R S_cls E) 0))))
                                    (show f ≠ (nb095_alpha_dummy_093 f) from (by
                                        unfold nb095_alpha_dummy_093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_095 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0168 D R S_cls E)
                                                  0)))) (show f ≠ (nb095_alpha_dummy_096 f) from
                                        (by
                                          unfold nb095_alpha_dummy_096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0169 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_013 D R S_cls E) from (by
          unfold nb095_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0164 D R S_cls E)
                  2)))) (show f ≠ (nb095_alpha_dummy_016 f) from (by
          unfold nb095_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0166 f) 2)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_012 D R S_cls E) from (by
          unfold nb095_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0164 D R S_cls E)
                  1)))) (show f ≠ (nb095_alpha_dummy_015 f) from (by
          unfold nb095_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0166 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_011 D R S_cls E) from (by
          unfold nb095_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0164 D R S_cls
                    E)
                  0)))) (show f ≠ (nb095_alpha_dummy_014 f) from (by
          unfold nb095_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0166 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_017 D R S_cls E) from (by
          unfold nb095_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0165 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_018 f) from (by
          unfold nb095_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0167 f) 0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x
        (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                  (nb095_split_alpha_0019 x u D R S_cls f E)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_170 D R S_cls E) from (by
          unfold nb095_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_172 f) from (by
          unfold nb095_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_012 D R S_cls E) ≠
        (nb095_alpha_dummy_169 D R S_cls E) from (by
          unfold nb095_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_171 f) from (by
          unfold nb095_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_012 D R S_cls E) ≠
        (nb095_alpha_dummy_199 D R S_cls E) from (by
          unfold nb095_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0204 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_200 f) from (by
          unfold nb095_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0205 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_012 D R S_cls E) ≠
        (nb095_alpha_dummy_173 D R S_cls E) from (by
          unfold nb095_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0201
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_174 f) from (by
          unfold nb095_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0203
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D
        R S_cls E)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_013 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_012 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_015 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095_split_alpha_0020 x u D R S_cls f E))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_170 D R S_cls E) from (by
          unfold nb095_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_172 f) from (by
          unfold nb095_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_012 D R S_cls E) ≠
        (nb095_alpha_dummy_169 D R S_cls E) from (by
          unfold nb095_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_171 f) from (by
          unfold nb095_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_012 D R S_cls E) ≠
        (nb095_alpha_dummy_199 D R S_cls E) from (by
          unfold nb095_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0204 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_200 f) from (by
          unfold nb095_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0205 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_012 D R S_cls E) ≠
        (nb095_alpha_dummy_173 D R S_cls E) from (by
          unfold nb095_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0201
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_174 f) from (by
          unfold nb095_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0203
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_ccnv (Class.cv (nb095_alpha_dummy_000 D
        R S_cls E)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_013 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_012 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_015 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095_split_alpha_0020 x u D R S_cls f E)))))))))))))) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                            (nb095_alpha_dummy_013 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_013;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E)
                                    2)))) (show f ≠ (nb095_alpha_dummy_016 f) from (by
                            unfold nb095_alpha_dummy_016;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0166 f) 2))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                              (nb095_alpha_dummy_012 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_012;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E)
                                      1)))) (show f ≠ (nb095_alpha_dummy_015 f) from (by
                              unfold nb095_alpha_dummy_015;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0166 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                (nb095_alpha_dummy_011 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_011;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0164 D R S_cls E) 0))))
                            (show f ≠ (nb095_alpha_dummy_014 f) from (by
                                unfold nb095_alpha_dummy_014;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0166 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                  (nb095_alpha_dummy_017 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0165 D R S_cls E) 0))))
                              (show f ≠ (nb095_alpha_dummy_018 f) from (by
                                  unfold nb095_alpha_dummy_018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0167 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u
                                (TAlphaVar.there (freshVar_injective
                                    ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide))
                                  dv_f_x (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
                    ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                  (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0022 x u D R S_cls f E))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                  (nb095_alpha_dummy_092 D R S_cls E) ≠
                                    (nb095_alpha_dummy_095 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_095;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0082 D R S_cls E) 0))))) (Ne.symm
                                (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_096 f) from
                                  (by
                                    unfold nb095_alpha_dummy_096;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0083 f)
                                            0))))) (TAlphaVar.there (Ne.symm (show
                                    (nb095_alpha_dummy_091 D R S_cls E) ≠
                                      (nb095_alpha_dummy_095 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_095;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0080 D R S_cls E) 0)))))
                                (Ne.symm (show
                                    (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_096 f) from
                                    (by
                                      unfold nb095_alpha_dummy_096;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0081 f)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.neg
                                        (nb095_split_alpha_0023 x u D R S_cls f E)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_098 D R S_cls E) from (by
          unfold nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold
            nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold
            nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091 D R
        S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0024 x u D R S_cls f E)))))))))
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_098 D R S_cls E) from (by
          unfold nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold
            nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold
            nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091 D R
        S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0024 x u D R S_cls f E)))))))))))))))))
                        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                        (nb095_split_alpha_0025 x u D R S_cls f E)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_134 D R S_cls E) from (by
          unfold nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold
            nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold
            nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0026 x u D R S_cls f E))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_134 D R S_cls E) from (by
          unfold nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold
            nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold
            nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0026 x u D R S_cls f E)))))))))))))))) (TAlphaClass.cv
                            (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                  (nb095_alpha_dummy_092 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0170 D R S_cls E) 1))))
                              (show f ≠ (nb095_alpha_dummy_094 f) from (by
                                  unfold nb095_alpha_dummy_094;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0171 f) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                    (nb095_alpha_dummy_091 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_091;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0170 D R S_cls E) 0))))
                                (show f ≠ (nb095_alpha_dummy_093 f) from (by
                                    unfold nb095_alpha_dummy_093;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0171 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_000 D R S_cls E) ≠
                                      (nb095_alpha_dummy_095 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_095;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0168 D R S_cls E) 0))))
                                  (show f ≠ (nb095_alpha_dummy_096 f) from (by
                                      unfold nb095_alpha_dummy_096;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0169 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_000 D R S_cls E) ≠
                                        (nb095_alpha_dummy_206 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0248 D R S_cls E) 1))))
                                    (show f ≠ (nb095_alpha_dummy_208 f) from (by
                                        unfold nb095_alpha_dummy_208;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0249 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_205 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0248 D R S_cls E)
                                                  0)))) (show f ≠ (nb095_alpha_dummy_207 f) from
                                        (by
                                          unfold nb095_alpha_dummy_207;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0249 f) 0))))
                                      (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide))
        dv_f_x (TAlphaVar.here _ _ _)))))))))))))))))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_247 D R S_cls E),
                              (nb095_alpha_dummy_248 x D R)),
                            ((nb095_alpha_dummy_245 D R S_cls E),
                              (nb095_alpha_dummy_246 x D R)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)] D
                          (nb095_focused_refl_0002 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_253 D R S_cls E) from (by
          unfold nb095_alpha_dummy_253;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0256 D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_254 x) from (by
          unfold nb095_alpha_dummy_254;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0257 x) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_250 D R S_cls E) from (by
          unfold nb095_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_252 x R) from (by
          unfold nb095_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_249 D R S_cls E) from (by
          unfold nb095_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095_alpha_dummy_251 x R) from (by
          unfold nb095_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_247 D R S_cls E) from (by
          unfold nb095_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_248 x D R) from (by
          unfold nb095_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_245 D R S_cls E) from (by
          unfold nb095_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_246 x D R) from (by
          unfold nb095_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _)))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0027 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_250
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095_split_alpha_0028 x u D R S_cls f E))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_250
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095_split_alpha_0028 x u D R S_cls f E)))))))))))))) (TAlphaClass.refl_of_reflOn
                                  [((nb095_alpha_dummy_250 D R S_cls E),
                                      (nb095_alpha_dummy_252 x R)),
                                    ((nb095_alpha_dummy_249 D R S_cls E),
                                      (nb095_alpha_dummy_251 x R)),
                                    ((nb095_alpha_dummy_247 D R S_cls E),
                                      (nb095_alpha_dummy_248 x D R)),
                                    ((nb095_alpha_dummy_245 D R S_cls E),
                                      (nb095_alpha_dummy_246 x D R)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_ccnv (syn_cdif R (syn_cid)))
                                  (nb095_wpp_refl_0100 x u D R S_cls f E dv_R_f dv_R_u
                                    dv_R_x)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_247 D R S_cls E),
                              (nb095_alpha_dummy_248 x D R)),
                            ((nb095_alpha_dummy_245 D R S_cls E),
                              (nb095_alpha_dummy_246 x D R)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)] D
                          (nb095_focused_refl_0002 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_253 D R S_cls E) from (by
          unfold nb095_alpha_dummy_253;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0256 D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_254 x) from (by
          unfold nb095_alpha_dummy_254;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0257 x) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_250 D R S_cls E) from (by
          unfold nb095_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_252 x R) from (by
          unfold nb095_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_249 D R S_cls E) from (by
          unfold nb095_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095_alpha_dummy_251 x R) from (by
          unfold nb095_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_247 D R S_cls E) from (by
          unfold nb095_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_248 x D R) from (by
          unfold nb095_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_245 D R S_cls E) from (by
          unfold nb095_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_246 x D R) from (by
          unfold nb095_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _)))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0027 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_250
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095_split_alpha_0028 x u D R S_cls f E))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_250
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095_split_alpha_0028 x u D R S_cls f E)))))))))))))) (TAlphaClass.refl_of_reflOn
                                  [((nb095_alpha_dummy_250 D R S_cls E),
                                      (nb095_alpha_dummy_252 x R)),
                                    ((nb095_alpha_dummy_249 D R S_cls E),
                                      (nb095_alpha_dummy_251 x R)),
                                    ((nb095_alpha_dummy_247 D R S_cls E),
                                      (nb095_alpha_dummy_248 x D R)),
                                    ((nb095_alpha_dummy_245 D R S_cls E),
                                      (nb095_alpha_dummy_246 x D R)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_ccnv (syn_cdif R (syn_cid)))
                                  (nb095_wpp_refl_0100 x u D R S_cls f E dv_R_f dv_R_u
                                    dv_R_x)))))))))))))))))

theorem nb095_compact_fv_empty_0222 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_293 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0223 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_294 u S_cls f E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0224 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_291 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0225 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_292 u S_cls f E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
