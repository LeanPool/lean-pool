/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C072C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C072C001Part012`. -/


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
noncomputable def nb072_split_alpha_0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_044 A B R S_cls H))
          (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
              (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_044 A B R S_cls H))
            (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_045 x y H))
          (Class.cab (nb072_alpha_dummy_040 x y H)
            (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_045 x y H))
            (Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                        (freshVar_injective (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H)
                              (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
                                  (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                                    (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))) (syn_csn
                                  (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv)
                          (by decide)) (freshVar_injective
                          (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
                                (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H
                                    (Class.cv (nb072_alpha_dummy_047 x H))))
                                (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv)
                          (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb072_split_alpha_0001 x y A B R S_cls H dv_x_y))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_055 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_057 x H) from (by
          unfold
            nb072_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_054 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_056 x H) from (by
          unfold
            nb072_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_084 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0082
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_085 x H) from (by
          unfold
            nb072_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0083
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_058 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0079
                    A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_059 x H) from (by
          unfold
            nb072_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0081
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_000 A
        B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072_split_alpha_0002 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_086 A B R S_cls H), (nb072_alpha_dummy_087 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_084 A B R S_cls H), (nb072_alpha_dummy_085 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_046 A B R S_cls H) ≠ (nb072_alpha_dummy_055 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_057 x H) from (by
          unfold
            nb072_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_054 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_056 x H) from (by
          unfold
            nb072_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_084 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0082
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_085 x H) from (by
          unfold
            nb072_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0083
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_058 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0079
                    A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_059 x H) from (by
          unfold
            nb072_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0081
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_000 A
        B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072_split_alpha_0002 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_086 A B R S_cls H), (nb072_alpha_dummy_087 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_084 A B R S_cls H), (nb072_alpha_dummy_085 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                [((nb072_alpha_dummy_046 A B R S_cls H),
                                    (nb072_alpha_dummy_047 x H)),
                                  ((nb072_alpha_dummy_048 A B R S_cls H),
                                    (nb072_alpha_dummy_049 x H)),
                                  ((nb072_alpha_dummy_051 A B R S_cls H),
                                    (nb072_alpha_dummy_053 x H)),
                                  ((nb072_alpha_dummy_050 A B R S_cls H),
                                    (nb072_alpha_dummy_052 x H)),
                                  ((nb072_alpha_dummy_039 A B R S_cls H),
                                    (nb072_alpha_dummy_041 x y H)),
                                  ((nb072_alpha_dummy_038 A B R S_cls H),
                                    (nb072_alpha_dummy_040 x y H)),
                                  ((nb072_alpha_dummy_044 A B R S_cls H),
                                    (nb072_alpha_dummy_045 x y H)),
                                  ((nb072_alpha_dummy_042 A B R S_cls H),
                                    (nb072_alpha_dummy_043 x y H)),
                                  ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                  ((nb072_alpha_dummy_000 A B R S_cls H), x)] H
                                (nb072_focused_refl_0003 x y A B R S_cls H dv_H_x dv_H_y))))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072_alpha_dummy_048 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_090 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0088 A B R S_cls H) 0)))) (show
                                    (nb072_alpha_dummy_049 x H) ≠ (nb072_alpha_dummy_091 x H)
                                    from (by
                                      unfold nb072_alpha_dummy_091;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0089 x H)
                                              0)))) (TAlphaVar.here _ _ _))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
                      ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv)
                    (by decide)) (freshVar_injective
                    (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb072_alpha_dummy_039 A B R S_cls H) ≠
                              (nb072_alpha_dummy_092 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_092;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0090 A B R S_cls H) 0)))) (show
                            (nb072_alpha_dummy_041 x y H) ≠ (nb072_alpha_dummy_094 x y H) from
                            (by
                              unfold nb072_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0091 x y H) 0))))
                          (TAlphaVar.there (show (nb072_alpha_dummy_039 A B R S_cls H) ≠
                                (nb072_alpha_dummy_093 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_093;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0090 A B R S_cls H) 1)))) (show
                              (nb072_alpha_dummy_041 x y H) ≠ (nb072_alpha_dummy_095 x y H) from
                              (by
                                unfold nb072_alpha_dummy_095;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0091 x y H)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_099 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_102 x y H) from
        (by
          unfold nb072_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095 x y H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_098 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_101 x y H) from
        (by
          unfold nb072_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095 x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)),
        ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)),
        ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)),
        ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)),
        ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)),
        ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)),
        ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R
        S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_110
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_111 x y H) from
        (by
          unfold
            nb072_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_110
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_111 x y H) from
        (by
          unfold
            nb072_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_112 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_113 x y H) from
        (by
          unfold
            nb072_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_112 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_113 x y H) from
        (by
          unfold
            nb072_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_092 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_096 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_096;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0092 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_094 x y H) ≠
                                        (nb072_alpha_dummy_097 x y H) from (by
                                        unfold nb072_alpha_dummy_097;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0093 x y H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb072_alpha_dummy_096 A B R S_cls H),
                                      (nb072_alpha_dummy_097 x y H)),
                                    ((nb072_alpha_dummy_092 A B R S_cls H),
                                      (nb072_alpha_dummy_094 x y H)),
                                    ((nb072_alpha_dummy_093 A B R S_cls H),
                                      (nb072_alpha_dummy_095 x y H)),
                                    ((nb072_alpha_dummy_039 A B R S_cls H),
                                      (nb072_alpha_dummy_041 x y H)),
                                    ((nb072_alpha_dummy_038 A B R S_cls H),
                                      (nb072_alpha_dummy_040 x y H)),
                                    ((nb072_alpha_dummy_044 A B R S_cls H),
                                      (nb072_alpha_dummy_045 x y H)),
                                    ((nb072_alpha_dummy_042 A B R S_cls H),
                                      (nb072_alpha_dummy_043 x y H)),
                                    ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                    ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072_alpha_dummy_092 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_096 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_096;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0092 A B R S_cls H) 0)))) (show
                                    (nb072_alpha_dummy_094 x y H) ≠
                                      (nb072_alpha_dummy_097 x y H) from (by
                                      unfold nb072_alpha_dummy_097;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0093 x y H) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_092 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_096 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_096;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0092 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_094 x y H) ≠
                                        (nb072_alpha_dummy_097 x y H) from (by
                                        unfold nb072_alpha_dummy_097;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0093 x y H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb072_alpha_dummy_096 A B R S_cls H),
                                      (nb072_alpha_dummy_097 x y H)),
                                    ((nb072_alpha_dummy_092 A B R S_cls H),
                                      (nb072_alpha_dummy_094 x y H)),
                                    ((nb072_alpha_dummy_093 A B R S_cls H),
                                      (nb072_alpha_dummy_095 x y H)),
                                    ((nb072_alpha_dummy_039 A B R S_cls H),
                                      (nb072_alpha_dummy_041 x y H)),
                                    ((nb072_alpha_dummy_038 A B R S_cls H),
                                      (nb072_alpha_dummy_040 x y H)),
                                    ((nb072_alpha_dummy_044 A B R S_cls H),
                                      (nb072_alpha_dummy_045 x y H)),
                                    ((nb072_alpha_dummy_042 A B R S_cls H),
                                      (nb072_alpha_dummy_043 x y H)),
                                    ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                    ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                          (freshVar_injective (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H)
                                (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
                                    (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                                      (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
                                  (syn_csn (Class.cv
                                      (nb072_alpha_dummy_048 A B R S_cls H)))))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
                                  (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H
                                      (Class.cv (nb072_alpha_dummy_047 x H))))
                                  (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072_split_alpha_0001 x y A B R S_cls H dv_x_y)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_055 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_057 x H) from (by
          unfold
            nb072_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_054 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_056 x H) from (by
          unfold
            nb072_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_084 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0082
                    A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_085 x H) from (by
          unfold
            nb072_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0083
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_058 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0079
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_059 x H) from (by
          unfold
            nb072_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0081
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_000 A B R S_cls
        H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072_split_alpha_0002 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_086 A B R S_cls H), (nb072_alpha_dummy_087 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_084 A B R S_cls H), (nb072_alpha_dummy_085 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_046 A B R S_cls H) ≠ (nb072_alpha_dummy_055 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_057 x H) from (by
          unfold
            nb072_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_054 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_056 x H) from (by
          unfold
            nb072_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_084 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0082
                    A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_085 x H) from (by
          unfold
            nb072_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0083
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_046 A B R S_cls H) ≠
        (nb072_alpha_dummy_058 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0079
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_047 x H) ≠ (nb072_alpha_dummy_059 x H) from (by
          unfold
            nb072_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0081
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_000 A B R S_cls
        H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072_split_alpha_0002 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_086 A B R S_cls H), (nb072_alpha_dummy_087 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_084 A B R S_cls H), (nb072_alpha_dummy_085 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                  [((nb072_alpha_dummy_046 A B R S_cls H),
                                      (nb072_alpha_dummy_047 x H)),
                                    ((nb072_alpha_dummy_048 A B R S_cls H),
                                      (nb072_alpha_dummy_049 x H)),
                                    ((nb072_alpha_dummy_051 A B R S_cls H),
                                      (nb072_alpha_dummy_053 x H)),
                                    ((nb072_alpha_dummy_050 A B R S_cls H),
                                      (nb072_alpha_dummy_052 x H)),
                                    ((nb072_alpha_dummy_039 A B R S_cls H),
                                      (nb072_alpha_dummy_041 x y H)),
                                    ((nb072_alpha_dummy_038 A B R S_cls H),
                                      (nb072_alpha_dummy_040 x y H)),
                                    ((nb072_alpha_dummy_044 A B R S_cls H),
                                      (nb072_alpha_dummy_045 x y H)),
                                    ((nb072_alpha_dummy_042 A B R S_cls H),
                                      (nb072_alpha_dummy_043 x y H)),
                                    ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                    ((nb072_alpha_dummy_000 A B R S_cls H), x)] H
                                  (nb072_focused_refl_0003 x y A B R S_cls H dv_H_x dv_H_y))))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_048 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_090 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_090;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0088 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_049 x H) ≠
                                        (nb072_alpha_dummy_091 x H) from (by
                                        unfold nb072_alpha_dummy_091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0089 x H) 0))))
                                    (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
                        ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv)
                      (by decide)) (freshVar_injective
                      (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072_alpha_dummy_039 A B R S_cls H) ≠
                                (nb072_alpha_dummy_092 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0090 A B R S_cls H) 0)))) (show
                              (nb072_alpha_dummy_041 x y H) ≠ (nb072_alpha_dummy_094 x y H) from
                              (by
                                unfold nb072_alpha_dummy_094;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0091 x y H)
                                        0)))) (TAlphaVar.there (show
                                (nb072_alpha_dummy_039 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_093 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_093;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0090 A B R S_cls H) 1)))) (show
                                (nb072_alpha_dummy_041 x y H) ≠ (nb072_alpha_dummy_095 x y H)
                                from (by
                                  unfold nb072_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0091 x y H)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_092 A B R S_cls H) ≠ (nb072_alpha_dummy_099 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_102 x y H) from
        (by
          unfold nb072_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095 x y H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_098 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_101 x y H) from
        (by
          unfold nb072_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095 x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B
                    R S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)),
        ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)),
        ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)),
        ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)),
        ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)),
        ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)),
        ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R
        S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_110
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_111 x y H) from
        (by
          unfold
            nb072_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_110
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_111 x y H) from
        (by
          unfold
            nb072_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_112 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_113 x y H) from
        (by
          unfold
            nb072_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_112 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_113 x y H) from
        (by
          unfold
            nb072_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0092 A B R S_cls H)
                                                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠
        (nb072_alpha_dummy_097 x y H) from (by
                                          unfold nb072_alpha_dummy_097;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0093 x y H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb072_alpha_dummy_096 A B R S_cls H),
                                        (nb072_alpha_dummy_097 x y H)),
                                      ((nb072_alpha_dummy_092 A B R S_cls H),
                                        (nb072_alpha_dummy_094 x y H)),
                                      ((nb072_alpha_dummy_093 A B R S_cls H),
                                        (nb072_alpha_dummy_095 x y H)),
                                      ((nb072_alpha_dummy_039 A B R S_cls H),
                                        (nb072_alpha_dummy_041 x y H)),
                                      ((nb072_alpha_dummy_038 A B R S_cls H),
                                        (nb072_alpha_dummy_040 x y H)),
                                      ((nb072_alpha_dummy_044 A B R S_cls H),
                                        (nb072_alpha_dummy_045 x y H)),
                                      ((nb072_alpha_dummy_042 A B R S_cls H),
                                        (nb072_alpha_dummy_043 x y H)),
                                      ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                      ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_092 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_096 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_096;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0092 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_094 x y H) ≠
                                        (nb072_alpha_dummy_097 x y H) from (by
                                        unfold nb072_alpha_dummy_097;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0093 x y H) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0092 A B R S_cls H)
                                                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠
        (nb072_alpha_dummy_097 x y H) from (by
                                          unfold nb072_alpha_dummy_097;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0093 x y H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb072_alpha_dummy_096 A B R S_cls H),
                                        (nb072_alpha_dummy_097 x y H)),
                                      ((nb072_alpha_dummy_092 A B R S_cls H),
                                        (nb072_alpha_dummy_094 x y H)),
                                      ((nb072_alpha_dummy_093 A B R S_cls H),
                                        (nb072_alpha_dummy_095 x y H)),
                                      ((nb072_alpha_dummy_039 A B R S_cls H),
                                        (nb072_alpha_dummy_041 x y H)),
                                      ((nb072_alpha_dummy_038 A B R S_cls H),
                                        (nb072_alpha_dummy_040 x y H)),
                                      ((nb072_alpha_dummy_044 A B R S_cls H),
                                        (nb072_alpha_dummy_045 x y H)),
                                      ((nb072_alpha_dummy_042 A B R S_cls H),
                                        (nb072_alpha_dummy_043 x y H)),
                                      ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                      ((nb072_alpha_dummy_000 A B R S_cls H), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C072C001Part013`. -/


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
noncomputable def nb072_split_alpha_0004 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) :
    TAlphaWff
      [((nb072_alpha_dummy_130 A B R S_cls H), (nb072_alpha_dummy_131 y H)),
        ((nb072_alpha_dummy_128 A B R S_cls H), (nb072_alpha_dummy_129 y H)),
        ((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_130 A B R S_cls H))
          (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_130 A B R S_cls H))
            (Class.cab (nb072_alpha_dummy_124 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_131 y H))
          (Class.cab (nb072_alpha_dummy_126 y H)
            (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_131 y H))
            (Class.cab (nb072_alpha_dummy_126 y H)
              (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                      (nb072_alpha_dummy_125 A B R S_cls H) from (by
                      unfold nb072_alpha_dummy_125;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 1))))
                  (show y ≠ (nb072_alpha_dummy_127 y H) from (by
                      unfold nb072_alpha_dummy_127;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0126 y H) 1)))) (TAlphaVar.there
                    (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                        (nb072_alpha_dummy_124 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_124;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H)
                                0)))) (show y ≠ (nb072_alpha_dummy_126 y H) from (by
                        unfold nb072_alpha_dummy_126;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                          (nb072_alpha_dummy_130 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0128 A B R S_cls H)
                                  0)))) (show y ≠ (nb072_alpha_dummy_131 y H) from (by
                          unfold nb072_alpha_dummy_131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0129 y H) 0))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                            (nb072_alpha_dummy_128 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0125 A B R S_cls H)
                                    0)))) (show y ≠ (nb072_alpha_dummy_129 y H) from (by
                            unfold nb072_alpha_dummy_129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0127 y H) 0))))
                        (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                              (nb072_alpha_dummy_116 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_116;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0118 A B R S_cls H) 0))))
                          (show y ≠ (nb072_alpha_dummy_117 y H) from (by
                              unfold nb072_alpha_dummy_117;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0121 y H) 0))))
                          (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                (nb072_alpha_dummy_118 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0119 A B R S_cls H) 0))))
                            (show y ≠ (nb072_alpha_dummy_119 y H) from (by
                                unfold nb072_alpha_dummy_119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0122 y H) 0))))
                            (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_121 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_121;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0120 A B R S_cls H) 1))))
                              (show y ≠ (nb072_alpha_dummy_123 y H) from (by
                                  unfold nb072_alpha_dummy_123;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0123 y H)
                                          1)))) (TAlphaVar.there (show
                                  (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                    (nb072_alpha_dummy_120 A B R S_cls H) from (by
                                    unfold nb072_alpha_dummy_120;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb072_support_mem_0120 A B R S_cls H) 0))))
                                (show y ≠ (nb072_alpha_dummy_122 y H) from (by
                                    unfold nb072_alpha_dummy_122;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb072_support_mem_0123 y H)
                                            0)))) (TAlphaVar.there (show
                                    (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_039 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_039;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0112 A B R S_cls H) 1))))
                                  (show y ≠ (nb072_alpha_dummy_041 x y H) from (by
                                      unfold nb072_alpha_dummy_041;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0114 x y H) 1))))
                                  (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_038 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_038;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0112 A B R S_cls H)
                                                0))))
                                    (show y ≠ (nb072_alpha_dummy_040 x y H) from (by
                                        unfold nb072_alpha_dummy_040;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0114 x y H) 0))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_001 A B R S_cls H) ≠
        (nb072_alpha_dummy_114 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_114;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0116 A B R S_cls H)
                                                  0))))
                                      (show y ≠ (nb072_alpha_dummy_115 x y H) from (by
                                          unfold nb072_alpha_dummy_115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0117 x y H) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_042 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0113 A B R S_cls H)
                  0)))) (show y ≠ (nb072_alpha_dummy_043 x y H) from (by
          unfold nb072_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0115 x y H) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
                      ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there (show
                            (nb072_alpha_dummy_125 A B R S_cls H) ≠
                              (nb072_alpha_dummy_132 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0130 A B R S_cls H) 0))))
                          (show (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_134 y H) from
                            (by
                              unfold nb072_alpha_dummy_134;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0131 y H) 0))))
                          (TAlphaVar.there (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                                (nb072_alpha_dummy_133 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_133;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0130 A B R S_cls H) 1)))) (show
                              (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_135 y H) from (by
                                unfold nb072_alpha_dummy_135;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0131 y H) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb072_alpha_dummy_127 y H))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_132 A B R S_cls H) ≠
        (nb072_alpha_dummy_139 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0134 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_142 y H) from (by
          unfold nb072_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0135 y H) 1)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_132 A B R S_cls H) ≠ (nb072_alpha_dummy_138 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0134 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_141 y H) from (by
          unfold nb072_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0135 y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_132 A B R S_cls H) ≠
        (nb072_alpha_dummy_136 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0132 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from (by
          unfold nb072_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0133 y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_140 A B R S_cls H), (nb072_alpha_dummy_143 y H)),
        ((nb072_alpha_dummy_139 A B R S_cls H), (nb072_alpha_dummy_142 y H)),
        ((nb072_alpha_dummy_138 A B R S_cls H), (nb072_alpha_dummy_141 y H)),
        ((nb072_alpha_dummy_136 A B R S_cls H), (nb072_alpha_dummy_137 y H)),
        ((nb072_alpha_dummy_132 A B R S_cls H), (nb072_alpha_dummy_134 y H)),
        ((nb072_alpha_dummy_133 A B R S_cls H), (nb072_alpha_dummy_135 y H)),
        ((nb072_alpha_dummy_125 A B R S_cls H), (nb072_alpha_dummy_127 y H)),
        ((nb072_alpha_dummy_124 A B R S_cls H), (nb072_alpha_dummy_126 y H)),
        ((nb072_alpha_dummy_130 A B R S_cls H), (nb072_alpha_dummy_131 y H)),
        ((nb072_alpha_dummy_128 A B R S_cls H), (nb072_alpha_dummy_129 y H)),
        ((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_146
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠ (nb072_alpha_dummy_146
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_146
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠ (nb072_alpha_dummy_146
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_140 A B R S_cls H), (nb072_alpha_dummy_143 y H)),
        ((nb072_alpha_dummy_139 A B R S_cls H), (nb072_alpha_dummy_142 y H)),
        ((nb072_alpha_dummy_138 A B R S_cls H), (nb072_alpha_dummy_141 y H)),
        ((nb072_alpha_dummy_136 A B R S_cls H), (nb072_alpha_dummy_137 y H)),
        ((nb072_alpha_dummy_132 A B R S_cls H), (nb072_alpha_dummy_134 y H)),
        ((nb072_alpha_dummy_133 A B R S_cls H), (nb072_alpha_dummy_135 y H)),
        ((nb072_alpha_dummy_125 A B R S_cls H), (nb072_alpha_dummy_127 y H)),
        ((nb072_alpha_dummy_124 A B R S_cls H), (nb072_alpha_dummy_126 y H)),
        ((nb072_alpha_dummy_130 A B R S_cls H), (nb072_alpha_dummy_131 y H)),
        ((nb072_alpha_dummy_128 A B R S_cls H), (nb072_alpha_dummy_129 y H)),
        ((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R
        S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_134 y
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_150
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_151 y H) from (by
          unfold
            nb072_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_150
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_151 y H) from (by
          unfold
            nb072_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_140
        A B R S_cls H) ≠ (nb072_alpha_dummy_152 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_153 y H) from (by
          unfold
            nb072_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_140
        A B R S_cls H) ≠ (nb072_alpha_dummy_152 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_153 y H) from (by
          unfold
            nb072_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0132 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_134 y H) ≠
                                        (nb072_alpha_dummy_137 y H) from (by
                                        unfold nb072_alpha_dummy_137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0133 y H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb072_alpha_dummy_136 A B R S_cls H),
                                      (nb072_alpha_dummy_137 y H)),
                                    ((nb072_alpha_dummy_132 A B R S_cls H),
                                      (nb072_alpha_dummy_134 y H)),
                                    ((nb072_alpha_dummy_133 A B R S_cls H),
                                      (nb072_alpha_dummy_135 y H)),
                                    ((nb072_alpha_dummy_125 A B R S_cls H),
                                      (nb072_alpha_dummy_127 y H)),
                                    ((nb072_alpha_dummy_124 A B R S_cls H),
                                      (nb072_alpha_dummy_126 y H)),
                                    ((nb072_alpha_dummy_130 A B R S_cls H),
                                      (nb072_alpha_dummy_131 y H)),
                                    ((nb072_alpha_dummy_128 A B R S_cls H),
                                      (nb072_alpha_dummy_129 y H)),
                                    ((nb072_alpha_dummy_116 A B R S_cls H),
                                      (nb072_alpha_dummy_117 y H)),
                                    ((nb072_alpha_dummy_118 A B R S_cls H),
                                      (nb072_alpha_dummy_119 y H)),
                                    ((nb072_alpha_dummy_121 A B R S_cls H),
                                      (nb072_alpha_dummy_123 y H)),
                                    ((nb072_alpha_dummy_120 A B R S_cls H),
                                      (nb072_alpha_dummy_122 y H)),
                                    ((nb072_alpha_dummy_039 A B R S_cls H),
                                      (nb072_alpha_dummy_041 x y H)),
                                    ((nb072_alpha_dummy_038 A B R S_cls H),
                                      (nb072_alpha_dummy_040 x y H)),
                                    ((nb072_alpha_dummy_114 A B R S_cls H),
                                      (nb072_alpha_dummy_115 x y H)),
                                    ((nb072_alpha_dummy_042 A B R S_cls H),
                                      (nb072_alpha_dummy_043 x y H)),
                                    ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                    ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_136;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0132 A B R S_cls H) 0)))) (show
                                    (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H)
                                    from (by
                                      unfold nb072_alpha_dummy_137;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0133 y H)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0132 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_134 y H) ≠
                                        (nb072_alpha_dummy_137 y H) from (by
                                        unfold nb072_alpha_dummy_137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0133 y H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb072_alpha_dummy_136 A B R S_cls H),
                                      (nb072_alpha_dummy_137 y H)),
                                    ((nb072_alpha_dummy_132 A B R S_cls H),
                                      (nb072_alpha_dummy_134 y H)),
                                    ((nb072_alpha_dummy_133 A B R S_cls H),
                                      (nb072_alpha_dummy_135 y H)),
                                    ((nb072_alpha_dummy_125 A B R S_cls H),
                                      (nb072_alpha_dummy_127 y H)),
                                    ((nb072_alpha_dummy_124 A B R S_cls H),
                                      (nb072_alpha_dummy_126 y H)),
                                    ((nb072_alpha_dummy_130 A B R S_cls H),
                                      (nb072_alpha_dummy_131 y H)),
                                    ((nb072_alpha_dummy_128 A B R S_cls H),
                                      (nb072_alpha_dummy_129 y H)),
                                    ((nb072_alpha_dummy_116 A B R S_cls H),
                                      (nb072_alpha_dummy_117 y H)),
                                    ((nb072_alpha_dummy_118 A B R S_cls H),
                                      (nb072_alpha_dummy_119 y H)),
                                    ((nb072_alpha_dummy_121 A B R S_cls H),
                                      (nb072_alpha_dummy_123 y H)),
                                    ((nb072_alpha_dummy_120 A B R S_cls H),
                                      (nb072_alpha_dummy_122 y H)),
                                    ((nb072_alpha_dummy_039 A B R S_cls H),
                                      (nb072_alpha_dummy_041 x y H)),
                                    ((nb072_alpha_dummy_038 A B R S_cls H),
                                      (nb072_alpha_dummy_040 x y H)),
                                    ((nb072_alpha_dummy_114 A B R S_cls H),
                                      (nb072_alpha_dummy_115 x y H)),
                                    ((nb072_alpha_dummy_042 A B R S_cls H),
                                      (nb072_alpha_dummy_043 x y H)),
                                    ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                    ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                        (nb072_alpha_dummy_125 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_125;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H)
                                1)))) (show y ≠ (nb072_alpha_dummy_127 y H) from (by
                        unfold nb072_alpha_dummy_127;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0126 y H) 1))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                          (nb072_alpha_dummy_124 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_124;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H)
                                  0)))) (show y ≠ (nb072_alpha_dummy_126 y H) from (by
                          unfold nb072_alpha_dummy_126;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                            (nb072_alpha_dummy_130 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_130;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0128 A B R S_cls H)
                                    0)))) (show y ≠ (nb072_alpha_dummy_131 y H) from (by
                            unfold nb072_alpha_dummy_131;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0129 y H) 0))))
                        (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                              (nb072_alpha_dummy_128 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_128;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0125 A B R S_cls H) 0))))
                          (show y ≠ (nb072_alpha_dummy_129 y H) from (by
                              unfold nb072_alpha_dummy_129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0127 y H) 0))))
                          (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                (nb072_alpha_dummy_116 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0118 A B R S_cls H) 0))))
                            (show y ≠ (nb072_alpha_dummy_117 y H) from (by
                                unfold nb072_alpha_dummy_117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0121 y H) 0))))
                            (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_118 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_118;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0119 A B R S_cls H) 0))))
                              (show y ≠ (nb072_alpha_dummy_119 y H) from (by
                                  unfold nb072_alpha_dummy_119;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0122 y H)
                                          0)))) (TAlphaVar.there (show
                                  (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                    (nb072_alpha_dummy_121 A B R S_cls H) from (by
                                    unfold nb072_alpha_dummy_121;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb072_support_mem_0120 A B R S_cls H) 1))))
                                (show y ≠ (nb072_alpha_dummy_123 y H) from (by
                                    unfold nb072_alpha_dummy_123;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb072_support_mem_0123 y H)
                                            1)))) (TAlphaVar.there (show
                                    (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_120 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_120;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0120 A B R S_cls H) 0))))
                                  (show y ≠ (nb072_alpha_dummy_122 y H) from (by
                                      unfold nb072_alpha_dummy_122;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0123 y H)
                                              0)))) (TAlphaVar.there (show
                                      (nb072_alpha_dummy_001 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_039 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_039;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0112 A B R S_cls H)
                                                1))))
                                    (show y ≠ (nb072_alpha_dummy_041 x y H) from (by
                                        unfold nb072_alpha_dummy_041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0114 x y H) 1))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_001 A B R S_cls H) ≠
        (nb072_alpha_dummy_038 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_038;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0112 A B R S_cls H)
                                                  0))))
                                      (show y ≠ (nb072_alpha_dummy_040 x y H) from (by
                                          unfold nb072_alpha_dummy_040;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0114 x y H) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_114 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0116 A B R S_cls H)
                  0)))) (show y ≠ (nb072_alpha_dummy_115 x y H) from (by
          unfold nb072_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0117 x y H) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_001 A B R S_cls H) ≠ (nb072_alpha_dummy_042 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0113 A B R S_cls
                    H)
                  0)))) (show y ≠ (nb072_alpha_dummy_043 x y H) from (by
          unfold nb072_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0115 x y H) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪
                        ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072_alpha_dummy_125 A B R S_cls H) ≠
                                (nb072_alpha_dummy_132 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0130 A B R S_cls H) 0)))) (show
                              (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_134 y H) from (by
                                unfold nb072_alpha_dummy_134;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0131 y H) 0))))
                            (TAlphaVar.there (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_133 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_133;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0130 A B R S_cls H) 1)))) (show
                                (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_135 y H) from
                                (by
                                  unfold nb072_alpha_dummy_135;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0131 y H)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb072_alpha_dummy_127 y H))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_132 A B R S_cls H) ≠ (nb072_alpha_dummy_139 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0134 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_142 y H) from (by
          unfold nb072_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0135 y H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_132 A B R S_cls H) ≠
        (nb072_alpha_dummy_138 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0134 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_141 y H) from (by
          unfold nb072_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0135 y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_132 A B R S_cls H) ≠
        (nb072_alpha_dummy_136 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0132 A B
                    R S_cls H)
                  0)))) (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from (by
          unfold nb072_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0133 y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_140 A B R S_cls H), (nb072_alpha_dummy_143 y H)),
        ((nb072_alpha_dummy_139 A B R S_cls H), (nb072_alpha_dummy_142 y H)),
        ((nb072_alpha_dummy_138 A B R S_cls H), (nb072_alpha_dummy_141 y H)),
        ((nb072_alpha_dummy_136 A B R S_cls H), (nb072_alpha_dummy_137 y H)),
        ((nb072_alpha_dummy_132 A B R S_cls H), (nb072_alpha_dummy_134 y H)),
        ((nb072_alpha_dummy_133 A B R S_cls H), (nb072_alpha_dummy_135 y H)),
        ((nb072_alpha_dummy_125 A B R S_cls H), (nb072_alpha_dummy_127 y H)),
        ((nb072_alpha_dummy_124 A B R S_cls H), (nb072_alpha_dummy_126 y H)),
        ((nb072_alpha_dummy_130 A B R S_cls H), (nb072_alpha_dummy_131 y H)),
        ((nb072_alpha_dummy_128 A B R S_cls H), (nb072_alpha_dummy_129 y H)),
        ((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_146
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠ (nb072_alpha_dummy_146
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_146
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠ (nb072_alpha_dummy_146
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_140 A B R S_cls H), (nb072_alpha_dummy_143 y H)),
        ((nb072_alpha_dummy_139 A B R S_cls H), (nb072_alpha_dummy_142 y H)),
        ((nb072_alpha_dummy_138 A B R S_cls H), (nb072_alpha_dummy_141 y H)),
        ((nb072_alpha_dummy_136 A B R S_cls H), (nb072_alpha_dummy_137 y H)),
        ((nb072_alpha_dummy_132 A B R S_cls H), (nb072_alpha_dummy_134 y H)),
        ((nb072_alpha_dummy_133 A B R S_cls H), (nb072_alpha_dummy_135 y H)),
        ((nb072_alpha_dummy_125 A B R S_cls H), (nb072_alpha_dummy_127 y H)),
        ((nb072_alpha_dummy_124 A B R S_cls H), (nb072_alpha_dummy_126 y H)),
        ((nb072_alpha_dummy_130 A B R S_cls H), (nb072_alpha_dummy_131 y H)),
        ((nb072_alpha_dummy_128 A B R S_cls H), (nb072_alpha_dummy_129 y H)),
        ((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R
        S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_134 y
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_150
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_151 y H) from (by
          unfold
            nb072_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_150
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_151 y H) from (by
          unfold
            nb072_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_140
        A B R S_cls H) ≠ (nb072_alpha_dummy_152 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_153 y H) from (by
          unfold
            nb072_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_140
        A B R S_cls H) ≠ (nb072_alpha_dummy_152 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_153 y H) from (by
          unfold
            nb072_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072_alpha_dummy_132 A B R S_cls H) ≠
        (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0132 A B R S_cls H)
                                                  0)))) (show (nb072_alpha_dummy_134 y H) ≠
        (nb072_alpha_dummy_137 y H) from (by
                                          unfold nb072_alpha_dummy_137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0133 y H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb072_alpha_dummy_136 A B R S_cls H),
                                        (nb072_alpha_dummy_137 y H)),
                                      ((nb072_alpha_dummy_132 A B R S_cls H),
                                        (nb072_alpha_dummy_134 y H)),
                                      ((nb072_alpha_dummy_133 A B R S_cls H),
                                        (nb072_alpha_dummy_135 y H)),
                                      ((nb072_alpha_dummy_125 A B R S_cls H),
                                        (nb072_alpha_dummy_127 y H)),
                                      ((nb072_alpha_dummy_124 A B R S_cls H),
                                        (nb072_alpha_dummy_126 y H)),
                                      ((nb072_alpha_dummy_130 A B R S_cls H),
                                        (nb072_alpha_dummy_131 y H)),
                                      ((nb072_alpha_dummy_128 A B R S_cls H),
                                        (nb072_alpha_dummy_129 y H)),
                                      ((nb072_alpha_dummy_116 A B R S_cls H),
                                        (nb072_alpha_dummy_117 y H)),
                                      ((nb072_alpha_dummy_118 A B R S_cls H),
                                        (nb072_alpha_dummy_119 y H)),
                                      ((nb072_alpha_dummy_121 A B R S_cls H),
                                        (nb072_alpha_dummy_123 y H)),
                                      ((nb072_alpha_dummy_120 A B R S_cls H),
                                        (nb072_alpha_dummy_122 y H)),
                                      ((nb072_alpha_dummy_039 A B R S_cls H),
                                        (nb072_alpha_dummy_041 x y H)),
                                      ((nb072_alpha_dummy_038 A B R S_cls H),
                                        (nb072_alpha_dummy_040 x y H)),
                                      ((nb072_alpha_dummy_114 A B R S_cls H),
                                        (nb072_alpha_dummy_115 x y H)),
                                      ((nb072_alpha_dummy_042 A B R S_cls H),
                                        (nb072_alpha_dummy_043 x y H)),
                                      ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                      ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0132 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_134 y H) ≠
                                        (nb072_alpha_dummy_137 y H) from (by
                                        unfold nb072_alpha_dummy_137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0133 y H) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072_alpha_dummy_132 A B R S_cls H) ≠
        (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0132 A B R S_cls H)
                                                  0)))) (show (nb072_alpha_dummy_134 y H) ≠
        (nb072_alpha_dummy_137 y H) from (by
                                          unfold nb072_alpha_dummy_137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0133 y H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb072_alpha_dummy_136 A B R S_cls H),
                                        (nb072_alpha_dummy_137 y H)),
                                      ((nb072_alpha_dummy_132 A B R S_cls H),
                                        (nb072_alpha_dummy_134 y H)),
                                      ((nb072_alpha_dummy_133 A B R S_cls H),
                                        (nb072_alpha_dummy_135 y H)),
                                      ((nb072_alpha_dummy_125 A B R S_cls H),
                                        (nb072_alpha_dummy_127 y H)),
                                      ((nb072_alpha_dummy_124 A B R S_cls H),
                                        (nb072_alpha_dummy_126 y H)),
                                      ((nb072_alpha_dummy_130 A B R S_cls H),
                                        (nb072_alpha_dummy_131 y H)),
                                      ((nb072_alpha_dummy_128 A B R S_cls H),
                                        (nb072_alpha_dummy_129 y H)),
                                      ((nb072_alpha_dummy_116 A B R S_cls H),
                                        (nb072_alpha_dummy_117 y H)),
                                      ((nb072_alpha_dummy_118 A B R S_cls H),
                                        (nb072_alpha_dummy_119 y H)),
                                      ((nb072_alpha_dummy_121 A B R S_cls H),
                                        (nb072_alpha_dummy_123 y H)),
                                      ((nb072_alpha_dummy_120 A B R S_cls H),
                                        (nb072_alpha_dummy_122 y H)),
                                      ((nb072_alpha_dummy_039 A B R S_cls H),
                                        (nb072_alpha_dummy_041 x y H)),
                                      ((nb072_alpha_dummy_038 A B R S_cls H),
                                        (nb072_alpha_dummy_040 x y H)),
                                      ((nb072_alpha_dummy_114 A B R S_cls H),
                                        (nb072_alpha_dummy_115 x y H)),
                                      ((nb072_alpha_dummy_042 A B R S_cls H),
                                        (nb072_alpha_dummy_043 x y H)),
                                      ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                      ((nb072_alpha_dummy_000 A B R S_cls H), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
