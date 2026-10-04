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

/-- Checked nominal proof certificate identified upstream as `nb072_split_alpha_0003`. -/
@[expose]
noncomputable def nb072SplitAlpha0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy044 A B R S_cls H))
          (Class.cab (nb072AlphaDummy038 A B R S_cls H)
            (synWrex (nb072AlphaDummy039 A B R S_cls H)
              (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
              (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy044 A B R S_cls H))
            (Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy045 x y H))
          (Class.cab (nb072AlphaDummy040 x y H)
            (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
              (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy045 x y H))
            (Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                        (freshVar_injective (((Class.cab (nb072AlphaDummy048 A B R S_cls H)
                              (Wff.classEq (Class.cab (nb072AlphaDummy046 A B R S_cls H)
                                  (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                                    (Class.cv (nb072AlphaDummy046 A B R S_cls H)))) (synCsn
                                  (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv)
                          (by decide)) (freshVar_injective
                          (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
                                (Class.cab (nb072AlphaDummy047 x H) (synWbr (Class.cv x) H
                                    (Class.cv (nb072AlphaDummy047 x H))))
                                (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv)
                          (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb072SplitAlpha0001 x y A B R S_cls H dv_x_y))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy055 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy057 x H) from (by
          unfold
            nb072AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy054 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy056 x H) from (by
          unfold
            nb072AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy084 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0082
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy085 x H) from (by
          unfold
            nb072AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0083
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy058 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0079
                    A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy059 x H) from (by
          unfold
            nb072AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0081
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy000 A
        B R S_cls H))).fv ∪ ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072SplitAlpha0002 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy086 A B R S_cls H), (nb072AlphaDummy087 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy084 A B R S_cls H), (nb072AlphaDummy085 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy046 A B R S_cls H) ≠ (nb072AlphaDummy055 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy057 x H) from (by
          unfold
            nb072AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy054 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy056 x H) from (by
          unfold
            nb072AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy084 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0082
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy085 x H) from (by
          unfold
            nb072AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0083
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy058 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0079
                    A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy059 x H) from (by
          unfold
            nb072AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0081
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy000 A
        B R S_cls H))).fv ∪ ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072SplitAlpha0002 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy086 A B R S_cls H), (nb072AlphaDummy087 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy084 A B R S_cls H), (nb072AlphaDummy085 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                [((nb072AlphaDummy046 A B R S_cls H),
                                    (nb072AlphaDummy047 x H)),
                                  ((nb072AlphaDummy048 A B R S_cls H),
                                    (nb072AlphaDummy049 x H)),
                                  ((nb072AlphaDummy051 A B R S_cls H),
                                    (nb072AlphaDummy053 x H)),
                                  ((nb072AlphaDummy050 A B R S_cls H),
                                    (nb072AlphaDummy052 x H)),
                                  ((nb072AlphaDummy039 A B R S_cls H),
                                    (nb072AlphaDummy041 x y H)),
                                  ((nb072AlphaDummy038 A B R S_cls H),
                                    (nb072AlphaDummy040 x y H)),
                                  ((nb072AlphaDummy044 A B R S_cls H),
                                    (nb072AlphaDummy045 x y H)),
                                  ((nb072AlphaDummy042 A B R S_cls H),
                                    (nb072AlphaDummy043 x y H)),
                                  ((nb072AlphaDummy001 A B R S_cls H), y),
                                  ((nb072AlphaDummy000 A B R S_cls H), x)] H
                                (nb072FocusedRefl0003 x y A B R S_cls H dv_H_x dv_H_y))))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072AlphaDummy048 A B R S_cls H) ≠
                                      (nb072AlphaDummy090 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0088 A B R S_cls H) 0)))) (show
                                    (nb072AlphaDummy049 x H) ≠ (nb072AlphaDummy091 x H)
                                    from (by
                                      unfold nb072AlphaDummy091;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0089 x H)
                                              0)))) (TAlphaVar.here _ _ _))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
                      ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv)
                    (by decide)) (freshVar_injective
                    (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb072AlphaDummy039 A B R S_cls H) ≠
                              (nb072AlphaDummy092 A B R S_cls H) from (by
                              unfold nb072AlphaDummy092;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0090 A B R S_cls H) 0)))) (show
                            (nb072AlphaDummy041 x y H) ≠ (nb072AlphaDummy094 x y H) from
                            (by
                              unfold nb072AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0091 x y H) 0))))
                          (TAlphaVar.there (show (nb072AlphaDummy039 A B R S_cls H) ≠
                                (nb072AlphaDummy093 A B R S_cls H) from (by
                                unfold nb072AlphaDummy093;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0090 A B R S_cls H) 1)))) (show
                              (nb072AlphaDummy041 x y H) ≠ (nb072AlphaDummy095 x y H) from
                              (by
                                unfold nb072AlphaDummy095;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0091 x y H)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb072AlphaDummy041 x y H))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy099 A B R S_cls H) from (by
          unfold nb072AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy102 x y H) from
        (by
          unfold nb072AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095 x y H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy098 A B R S_cls H) from (by
          unfold nb072AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy101 x y H) from
        (by
          unfold nb072AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095 x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy096 A B R S_cls H) from (by
          unfold nb072AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy097 x y H) from
        (by
          unfold nb072AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy100 A B R S_cls H), (nb072AlphaDummy103 x y H)),
        ((nb072AlphaDummy099 A B R S_cls H), (nb072AlphaDummy102 x y H)),
        ((nb072AlphaDummy098 A B R S_cls H), (nb072AlphaDummy101 x y H)),
        ((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠ (nb072AlphaDummy106
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy105 x y H) from
        (by
          unfold
            nb072AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠ (nb072AlphaDummy106
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy105 x y H) from
        (by
          unfold
            nb072AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠ (nb072AlphaDummy106
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy105 x y H) from
        (by
          unfold
            nb072AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠ (nb072AlphaDummy106
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy105 x y H) from
        (by
          unfold
            nb072AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy100 A B R S_cls H), (nb072AlphaDummy103 x y H)),
        ((nb072AlphaDummy099 A B R S_cls H), (nb072AlphaDummy102 x y H)),
        ((nb072AlphaDummy098 A B R S_cls H), (nb072AlphaDummy101 x y H)),
        ((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092 A B R
        S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y
        H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠ (nb072AlphaDummy110
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy111 x y H) from
        (by
          unfold
            nb072AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy109 x y H) from
        (by
          unfold
            nb072AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠ (nb072AlphaDummy110
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy111 x y H) from
        (by
          unfold
            nb072AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy109 x y H) from
        (by
          unfold
            nb072AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy100
        A B R S_cls H) ≠ (nb072AlphaDummy112 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy113 x y H) from
        (by
          unfold
            nb072AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy109 x y H) from
        (by
          unfold
            nb072AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy100
        A B R S_cls H) ≠ (nb072AlphaDummy112 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy113 x y H) from
        (by
          unfold
            nb072AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy109 x y H) from
        (by
          unfold
            nb072AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy092 A B R S_cls H) ≠
                                        (nb072AlphaDummy096 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy096;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0092 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy094 x y H) ≠
                                        (nb072AlphaDummy097 x y H) from (by
                                        unfold nb072AlphaDummy097;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0093 x y H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb072AlphaDummy096 A B R S_cls H),
                                      (nb072AlphaDummy097 x y H)),
                                    ((nb072AlphaDummy092 A B R S_cls H),
                                      (nb072AlphaDummy094 x y H)),
                                    ((nb072AlphaDummy093 A B R S_cls H),
                                      (nb072AlphaDummy095 x y H)),
                                    ((nb072AlphaDummy039 A B R S_cls H),
                                      (nb072AlphaDummy041 x y H)),
                                    ((nb072AlphaDummy038 A B R S_cls H),
                                      (nb072AlphaDummy040 x y H)),
                                    ((nb072AlphaDummy044 A B R S_cls H),
                                      (nb072AlphaDummy045 x y H)),
                                    ((nb072AlphaDummy042 A B R S_cls H),
                                      (nb072AlphaDummy043 x y H)),
                                    ((nb072AlphaDummy001 A B R S_cls H), y),
                                    ((nb072AlphaDummy000 A B R S_cls H), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072AlphaDummy092 A B R S_cls H) ≠
                                      (nb072AlphaDummy096 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy096;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0092 A B R S_cls H) 0)))) (show
                                    (nb072AlphaDummy094 x y H) ≠
                                      (nb072AlphaDummy097 x y H) from (by
                                      unfold nb072AlphaDummy097;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0093 x y H) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy092 A B R S_cls H) ≠
                                        (nb072AlphaDummy096 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy096;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0092 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy094 x y H) ≠
                                        (nb072AlphaDummy097 x y H) from (by
                                        unfold nb072AlphaDummy097;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0093 x y H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb072AlphaDummy096 A B R S_cls H),
                                      (nb072AlphaDummy097 x y H)),
                                    ((nb072AlphaDummy092 A B R S_cls H),
                                      (nb072AlphaDummy094 x y H)),
                                    ((nb072AlphaDummy093 A B R S_cls H),
                                      (nb072AlphaDummy095 x y H)),
                                    ((nb072AlphaDummy039 A B R S_cls H),
                                      (nb072AlphaDummy041 x y H)),
                                    ((nb072AlphaDummy038 A B R S_cls H),
                                      (nb072AlphaDummy040 x y H)),
                                    ((nb072AlphaDummy044 A B R S_cls H),
                                      (nb072AlphaDummy045 x y H)),
                                    ((nb072AlphaDummy042 A B R S_cls H),
                                      (nb072AlphaDummy043 x y H)),
                                    ((nb072AlphaDummy001 A B R S_cls H), y),
                                    ((nb072AlphaDummy000 A B R S_cls H), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                          (freshVar_injective (((Class.cab (nb072AlphaDummy048 A B R S_cls H)
                                (Wff.classEq (Class.cab (nb072AlphaDummy046 A B R S_cls H)
                                    (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                                      (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
                                  (synCsn (Class.cv
                                      (nb072AlphaDummy048 A B R S_cls H)))))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
                                  (Class.cab (nb072AlphaDummy047 x H) (synWbr (Class.cv x) H
                                      (Class.cv (nb072AlphaDummy047 x H))))
                                  (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072SplitAlpha0001 x y A B R S_cls H dv_x_y)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy055 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy057 x H) from (by
          unfold
            nb072AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy054 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy056 x H) from (by
          unfold
            nb072AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy084 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0082
                    A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy085 x H) from (by
          unfold
            nb072AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0083
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy058 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0079
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy059 x H) from (by
          unfold
            nb072AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0081
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy000 A B R S_cls
        H))).fv ∪ ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072SplitAlpha0002 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy086 A B R S_cls H), (nb072AlphaDummy087 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy084 A B R S_cls H), (nb072AlphaDummy085 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy046 A B R S_cls H) ≠ (nb072AlphaDummy055 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy057 x H) from (by
          unfold
            nb072AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy054 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0078
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy056 x H) from (by
          unfold
            nb072AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0080
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy084 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0082
                    A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy085 x H) from (by
          unfold
            nb072AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0083
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy046 A B R S_cls H) ≠
        (nb072AlphaDummy058 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0079
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy047 x H) ≠ (nb072AlphaDummy059 x H) from (by
          unfold
            nb072AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0081
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy000 A B R S_cls
        H))).fv ∪ ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072SplitAlpha0002 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy086 A B R S_cls H), (nb072AlphaDummy087 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy084 A B R S_cls H), (nb072AlphaDummy085 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb072AlphaDummy046 A B R S_cls H),
                                      (nb072AlphaDummy047 x H)),
                                    ((nb072AlphaDummy048 A B R S_cls H),
                                      (nb072AlphaDummy049 x H)),
                                    ((nb072AlphaDummy051 A B R S_cls H),
                                      (nb072AlphaDummy053 x H)),
                                    ((nb072AlphaDummy050 A B R S_cls H),
                                      (nb072AlphaDummy052 x H)),
                                    ((nb072AlphaDummy039 A B R S_cls H),
                                      (nb072AlphaDummy041 x y H)),
                                    ((nb072AlphaDummy038 A B R S_cls H),
                                      (nb072AlphaDummy040 x y H)),
                                    ((nb072AlphaDummy044 A B R S_cls H),
                                      (nb072AlphaDummy045 x y H)),
                                    ((nb072AlphaDummy042 A B R S_cls H),
                                      (nb072AlphaDummy043 x y H)),
                                    ((nb072AlphaDummy001 A B R S_cls H), y),
                                    ((nb072AlphaDummy000 A B R S_cls H), x)] H
                                  (nb072FocusedRefl0003 x y A B R S_cls H dv_H_x dv_H_y))))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy048 A B R S_cls H) ≠
                                        (nb072AlphaDummy090 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy090;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0088 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy049 x H) ≠
                                        (nb072AlphaDummy091 x H) from (by
                                        unfold nb072AlphaDummy091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0089 x H) 0))))
                                    (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
                        ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv)
                      (by decide)) (freshVar_injective
                      (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072AlphaDummy039 A B R S_cls H) ≠
                                (nb072AlphaDummy092 A B R S_cls H) from (by
                                unfold nb072AlphaDummy092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0090 A B R S_cls H) 0)))) (show
                              (nb072AlphaDummy041 x y H) ≠ (nb072AlphaDummy094 x y H) from
                              (by
                                unfold nb072AlphaDummy094;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0091 x y H)
                                        0)))) (TAlphaVar.there (show
                                (nb072AlphaDummy039 A B R S_cls H) ≠
                                  (nb072AlphaDummy093 A B R S_cls H) from (by
                                  unfold nb072AlphaDummy093;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0090 A B R S_cls H) 1)))) (show
                                (nb072AlphaDummy041 x y H) ≠ (nb072AlphaDummy095 x y H)
                                from (by
                                  unfold nb072AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0091 x y H)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb072AlphaDummy039 A B R S_cls H))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb072AlphaDummy041 x y H))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy092 A B R S_cls H) ≠ (nb072AlphaDummy099 A B R S_cls H) from (by
          unfold nb072AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy102 x y H) from
        (by
          unfold nb072AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095 x y H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy098 A B R S_cls H) from (by
          unfold nb072AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy101 x y H) from
        (by
          unfold nb072AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095 x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy096 A B R S_cls H) from (by
          unfold nb072AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B
                    R S_cls H)
                  0)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy097 x y H) from
        (by
          unfold nb072AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy100 A B R S_cls H), (nb072AlphaDummy103 x y H)),
        ((nb072AlphaDummy099 A B R S_cls H), (nb072AlphaDummy102 x y H)),
        ((nb072AlphaDummy098 A B R S_cls H), (nb072AlphaDummy101 x y H)),
        ((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠ (nb072AlphaDummy106
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy105 x y H) from
        (by
          unfold
            nb072AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠ (nb072AlphaDummy106
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy105 x y H) from
        (by
          unfold
            nb072AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠ (nb072AlphaDummy106
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy105 x y H) from
        (by
          unfold
            nb072AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠ (nb072AlphaDummy106
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy105 x y H) from
        (by
          unfold
            nb072AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy100 A B R S_cls H), (nb072AlphaDummy103 x y H)),
        ((nb072AlphaDummy099 A B R S_cls H), (nb072AlphaDummy102 x y H)),
        ((nb072AlphaDummy098 A B R S_cls H), (nb072AlphaDummy101 x y H)),
        ((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092 A B R
        S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y
        H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠ (nb072AlphaDummy110
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy111 x y H) from
        (by
          unfold
            nb072AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy109 x y H) from
        (by
          unfold
            nb072AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠ (nb072AlphaDummy110
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy111 x y H) from
        (by
          unfold
            nb072AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy109 x y H) from
        (by
          unfold
            nb072AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy100
        A B R S_cls H) ≠ (nb072AlphaDummy112 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy113 x y H) from
        (by
          unfold
            nb072AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy109 x y H) from
        (by
          unfold
            nb072AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy100
        A B R S_cls H) ≠ (nb072AlphaDummy112 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy113 x y H) from
        (by
          unfold
            nb072AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy109 x y H) from
        (by
          unfold
            nb072AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy096 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0092 A B R S_cls H)
                                                  0)))) (show (nb072AlphaDummy094 x y H) ≠
        (nb072AlphaDummy097 x y H) from (by
                                          unfold nb072AlphaDummy097;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0093 x y H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb072AlphaDummy096 A B R S_cls H),
                                        (nb072AlphaDummy097 x y H)),
                                      ((nb072AlphaDummy092 A B R S_cls H),
                                        (nb072AlphaDummy094 x y H)),
                                      ((nb072AlphaDummy093 A B R S_cls H),
                                        (nb072AlphaDummy095 x y H)),
                                      ((nb072AlphaDummy039 A B R S_cls H),
                                        (nb072AlphaDummy041 x y H)),
                                      ((nb072AlphaDummy038 A B R S_cls H),
                                        (nb072AlphaDummy040 x y H)),
                                      ((nb072AlphaDummy044 A B R S_cls H),
                                        (nb072AlphaDummy045 x y H)),
                                      ((nb072AlphaDummy042 A B R S_cls H),
                                        (nb072AlphaDummy043 x y H)),
                                      ((nb072AlphaDummy001 A B R S_cls H), y),
                                      ((nb072AlphaDummy000 A B R S_cls H), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy092 A B R S_cls H) ≠
                                        (nb072AlphaDummy096 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy096;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0092 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy094 x y H) ≠
                                        (nb072AlphaDummy097 x y H) from (by
                                        unfold nb072AlphaDummy097;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0093 x y H) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy096 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0092 A B R S_cls H)
                                                  0)))) (show (nb072AlphaDummy094 x y H) ≠
        (nb072AlphaDummy097 x y H) from (by
                                          unfold nb072AlphaDummy097;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0093 x y H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb072AlphaDummy096 A B R S_cls H),
                                        (nb072AlphaDummy097 x y H)),
                                      ((nb072AlphaDummy092 A B R S_cls H),
                                        (nb072AlphaDummy094 x y H)),
                                      ((nb072AlphaDummy093 A B R S_cls H),
                                        (nb072AlphaDummy095 x y H)),
                                      ((nb072AlphaDummy039 A B R S_cls H),
                                        (nb072AlphaDummy041 x y H)),
                                      ((nb072AlphaDummy038 A B R S_cls H),
                                        (nb072AlphaDummy040 x y H)),
                                      ((nb072AlphaDummy044 A B R S_cls H),
                                        (nb072AlphaDummy045 x y H)),
                                      ((nb072AlphaDummy042 A B R S_cls H),
                                        (nb072AlphaDummy043 x y H)),
                                      ((nb072AlphaDummy001 A B R S_cls H), y),
                                      ((nb072AlphaDummy000 A B R S_cls H), x)] (synCnnc)
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

/-- Checked nominal proof certificate identified upstream as `nb072_split_alpha_0004`. -/
@[expose]
noncomputable def nb072SplitAlpha0004 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) :
    TAlphaWff
      [((nb072AlphaDummy130 A B R S_cls H), (nb072AlphaDummy131 y H)),
        ((nb072AlphaDummy128 A B R S_cls H), (nb072AlphaDummy129 y H)),
        ((nb072AlphaDummy116 A B R S_cls H), (nb072AlphaDummy117 y H)),
        ((nb072AlphaDummy118 A B R S_cls H), (nb072AlphaDummy119 y H)),
        ((nb072AlphaDummy121 A B R S_cls H), (nb072AlphaDummy123 y H)),
        ((nb072AlphaDummy120 A B R S_cls H), (nb072AlphaDummy122 y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy130 A B R S_cls H))
          (Class.cab (nb072AlphaDummy124 A B R S_cls H)
            (synWrex (nb072AlphaDummy125 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy130 A B R S_cls H))
            (Class.cab (nb072AlphaDummy124 A B R S_cls H)
              (synWrex (nb072AlphaDummy125 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy124 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy125 A B R S_cls H)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy131 y H))
          (Class.cab (nb072AlphaDummy126 y H)
            (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                (synCphi (Class.cv (nb072AlphaDummy127 y H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy131 y H))
            (Class.cab (nb072AlphaDummy126 y H)
              (synWrex (nb072AlphaDummy127 y H) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy126 y H))
                  (synCphi (Class.cv (nb072AlphaDummy127 y H))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                      (nb072AlphaDummy125 A B R S_cls H) from (by
                      unfold nb072AlphaDummy125;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 1))))
                  (show y ≠ (nb072AlphaDummy127 y H) from (by
                      unfold nb072AlphaDummy127;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0126 y H) 1)))) (TAlphaVar.there
                    (show (nb072AlphaDummy001 A B R S_cls H) ≠
                        (nb072AlphaDummy124 A B R S_cls H) from (by
                        unfold nb072AlphaDummy124;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H)
                                0)))) (show y ≠ (nb072AlphaDummy126 y H) from (by
                        unfold nb072AlphaDummy126;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))))
                    (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                          (nb072AlphaDummy130 A B R S_cls H) from (by
                          unfold nb072AlphaDummy130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0128 A B R S_cls H)
                                  0)))) (show y ≠ (nb072AlphaDummy131 y H) from (by
                          unfold nb072AlphaDummy131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0129 y H) 0))))
                      (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                            (nb072AlphaDummy128 A B R S_cls H) from (by
                            unfold nb072AlphaDummy128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0125 A B R S_cls H)
                                    0)))) (show y ≠ (nb072AlphaDummy129 y H) from (by
                            unfold nb072AlphaDummy129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0127 y H) 0))))
                        (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                              (nb072AlphaDummy116 A B R S_cls H) from (by
                              unfold nb072AlphaDummy116;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0118 A B R S_cls H) 0))))
                          (show y ≠ (nb072AlphaDummy117 y H) from (by
                              unfold nb072AlphaDummy117;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0121 y H) 0))))
                          (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                                (nb072AlphaDummy118 A B R S_cls H) from (by
                                unfold nb072AlphaDummy118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0119 A B R S_cls H) 0))))
                            (show y ≠ (nb072AlphaDummy119 y H) from (by
                                unfold nb072AlphaDummy119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0122 y H) 0))))
                            (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                                  (nb072AlphaDummy121 A B R S_cls H) from (by
                                  unfold nb072AlphaDummy121;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0120 A B R S_cls H) 1))))
                              (show y ≠ (nb072AlphaDummy123 y H) from (by
                                  unfold nb072AlphaDummy123;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0123 y H)
                                          1)))) (TAlphaVar.there (show
                                  (nb072AlphaDummy001 A B R S_cls H) ≠
                                    (nb072AlphaDummy120 A B R S_cls H) from (by
                                    unfold nb072AlphaDummy120;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb072_support_mem_0120 A B R S_cls H) 0))))
                                (show y ≠ (nb072AlphaDummy122 y H) from (by
                                    unfold nb072AlphaDummy122;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb072_support_mem_0123 y H)
                                            0)))) (TAlphaVar.there (show
                                    (nb072AlphaDummy001 A B R S_cls H) ≠
                                      (nb072AlphaDummy039 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy039;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0112 A B R S_cls H) 1))))
                                  (show y ≠ (nb072AlphaDummy041 x y H) from (by
                                      unfold nb072AlphaDummy041;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0114 x y H) 1))))
                                  (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                                        (nb072AlphaDummy038 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy038;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0112 A B R S_cls H)
                                                0))))
                                    (show y ≠ (nb072AlphaDummy040 x y H) from (by
                                        unfold nb072AlphaDummy040;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0114 x y H) 0))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy001 A B R S_cls H) ≠
        (nb072AlphaDummy114 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy114;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0116 A B R S_cls H)
                                                  0))))
                                      (show y ≠ (nb072AlphaDummy115 x y H) from (by
                                          unfold nb072AlphaDummy115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0117 x y H) 0))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy042 A B R S_cls H) from (by
          unfold nb072AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0113 A B R S_cls H)
                  0)))) (show y ≠ (nb072AlphaDummy043 x y H) from (by
          unfold nb072AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0115 x y H) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
                      ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there (show
                            (nb072AlphaDummy125 A B R S_cls H) ≠
                              (nb072AlphaDummy132 A B R S_cls H) from (by
                              unfold nb072AlphaDummy132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0130 A B R S_cls H) 0))))
                          (show (nb072AlphaDummy127 y H) ≠ (nb072AlphaDummy134 y H) from
                            (by
                              unfold nb072AlphaDummy134;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0131 y H) 0))))
                          (TAlphaVar.there (show (nb072AlphaDummy125 A B R S_cls H) ≠
                                (nb072AlphaDummy133 A B R S_cls H) from (by
                                unfold nb072AlphaDummy133;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0130 A B R S_cls H) 1)))) (show
                              (nb072AlphaDummy127 y H) ≠ (nb072AlphaDummy135 y H) from (by
                                unfold nb072AlphaDummy135;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0131 y H) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb072AlphaDummy127 y H))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy132 A B R S_cls H) ≠
        (nb072AlphaDummy139 A B R S_cls H) from (by
          unfold nb072AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0134 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy134 y H) ≠ (nb072AlphaDummy142 y H) from (by
          unfold nb072AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0135 y H) 1)))) (TAlphaVar.there (show
        (nb072AlphaDummy132 A B R S_cls H) ≠ (nb072AlphaDummy138 A B R S_cls H) from (by
          unfold nb072AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0134 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy134 y H) ≠ (nb072AlphaDummy141 y H) from (by
          unfold nb072AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0135 y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy132 A B R S_cls H) ≠
        (nb072AlphaDummy136 A B R S_cls H) from (by
          unfold nb072AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0132 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy134 y H) ≠ (nb072AlphaDummy137 y H) from (by
          unfold nb072AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0133 y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy140 A B R S_cls H), (nb072AlphaDummy143 y H)),
        ((nb072AlphaDummy139 A B R S_cls H), (nb072AlphaDummy142 y H)),
        ((nb072AlphaDummy138 A B R S_cls H), (nb072AlphaDummy141 y H)),
        ((nb072AlphaDummy136 A B R S_cls H), (nb072AlphaDummy137 y H)),
        ((nb072AlphaDummy132 A B R S_cls H), (nb072AlphaDummy134 y H)),
        ((nb072AlphaDummy133 A B R S_cls H), (nb072AlphaDummy135 y H)),
        ((nb072AlphaDummy125 A B R S_cls H), (nb072AlphaDummy127 y H)),
        ((nb072AlphaDummy124 A B R S_cls H), (nb072AlphaDummy126 y H)),
        ((nb072AlphaDummy130 A B R S_cls H), (nb072AlphaDummy131 y H)),
        ((nb072AlphaDummy128 A B R S_cls H), (nb072AlphaDummy129 y H)),
        ((nb072AlphaDummy116 A B R S_cls H), (nb072AlphaDummy117 y H)),
        ((nb072AlphaDummy118 A B R S_cls H), (nb072AlphaDummy119 y H)),
        ((nb072AlphaDummy121 A B R S_cls H), (nb072AlphaDummy123 y H)),
        ((nb072AlphaDummy120 A B R S_cls H), (nb072AlphaDummy122 y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠ (nb072AlphaDummy146
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy147 y H) from (by
          unfold
            nb072AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠
        (nb072AlphaDummy144 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy145 y H) from (by
          unfold
            nb072AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠ (nb072AlphaDummy146
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy147 y H) from (by
          unfold
            nb072AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠
        (nb072AlphaDummy144 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy145 y H) from (by
          unfold
            nb072AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠ (nb072AlphaDummy146
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy147 y H) from (by
          unfold
            nb072AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠
        (nb072AlphaDummy144 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy145 y H) from (by
          unfold
            nb072AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠ (nb072AlphaDummy146
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy147 y H) from (by
          unfold
            nb072AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠
        (nb072AlphaDummy144 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy145 y H) from (by
          unfold
            nb072AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy140 A B R S_cls H), (nb072AlphaDummy143 y H)),
        ((nb072AlphaDummy139 A B R S_cls H), (nb072AlphaDummy142 y H)),
        ((nb072AlphaDummy138 A B R S_cls H), (nb072AlphaDummy141 y H)),
        ((nb072AlphaDummy136 A B R S_cls H), (nb072AlphaDummy137 y H)),
        ((nb072AlphaDummy132 A B R S_cls H), (nb072AlphaDummy134 y H)),
        ((nb072AlphaDummy133 A B R S_cls H), (nb072AlphaDummy135 y H)),
        ((nb072AlphaDummy125 A B R S_cls H), (nb072AlphaDummy127 y H)),
        ((nb072AlphaDummy124 A B R S_cls H), (nb072AlphaDummy126 y H)),
        ((nb072AlphaDummy130 A B R S_cls H), (nb072AlphaDummy131 y H)),
        ((nb072AlphaDummy128 A B R S_cls H), (nb072AlphaDummy129 y H)),
        ((nb072AlphaDummy116 A B R S_cls H), (nb072AlphaDummy117 y H)),
        ((nb072AlphaDummy118 A B R S_cls H), (nb072AlphaDummy119 y H)),
        ((nb072AlphaDummy121 A B R S_cls H), (nb072AlphaDummy123 y H)),
        ((nb072AlphaDummy120 A B R S_cls H), (nb072AlphaDummy122 y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132 A B R
        S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy134 y
        H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠ (nb072AlphaDummy150
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy151 y H) from (by
          unfold
            nb072AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠
        (nb072AlphaDummy148 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy149 y H) from (by
          unfold
            nb072AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠ (nb072AlphaDummy150
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy151 y H) from (by
          unfold
            nb072AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠
        (nb072AlphaDummy148 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy149 y H) from (by
          unfold
            nb072AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy140
        A B R S_cls H) ≠ (nb072AlphaDummy152 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy153 y H) from (by
          unfold
            nb072AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠
        (nb072AlphaDummy148 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy149 y H) from (by
          unfold
            nb072AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy140
        A B R S_cls H) ≠ (nb072AlphaDummy152 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy153 y H) from (by
          unfold
            nb072AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠
        (nb072AlphaDummy148 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy149 y H) from (by
          unfold
            nb072AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy132 A B R S_cls H) ≠
                                        (nb072AlphaDummy136 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0132 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy134 y H) ≠
                                        (nb072AlphaDummy137 y H) from (by
                                        unfold nb072AlphaDummy137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0133 y H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb072AlphaDummy136 A B R S_cls H),
                                      (nb072AlphaDummy137 y H)),
                                    ((nb072AlphaDummy132 A B R S_cls H),
                                      (nb072AlphaDummy134 y H)),
                                    ((nb072AlphaDummy133 A B R S_cls H),
                                      (nb072AlphaDummy135 y H)),
                                    ((nb072AlphaDummy125 A B R S_cls H),
                                      (nb072AlphaDummy127 y H)),
                                    ((nb072AlphaDummy124 A B R S_cls H),
                                      (nb072AlphaDummy126 y H)),
                                    ((nb072AlphaDummy130 A B R S_cls H),
                                      (nb072AlphaDummy131 y H)),
                                    ((nb072AlphaDummy128 A B R S_cls H),
                                      (nb072AlphaDummy129 y H)),
                                    ((nb072AlphaDummy116 A B R S_cls H),
                                      (nb072AlphaDummy117 y H)),
                                    ((nb072AlphaDummy118 A B R S_cls H),
                                      (nb072AlphaDummy119 y H)),
                                    ((nb072AlphaDummy121 A B R S_cls H),
                                      (nb072AlphaDummy123 y H)),
                                    ((nb072AlphaDummy120 A B R S_cls H),
                                      (nb072AlphaDummy122 y H)),
                                    ((nb072AlphaDummy039 A B R S_cls H),
                                      (nb072AlphaDummy041 x y H)),
                                    ((nb072AlphaDummy038 A B R S_cls H),
                                      (nb072AlphaDummy040 x y H)),
                                    ((nb072AlphaDummy114 A B R S_cls H),
                                      (nb072AlphaDummy115 x y H)),
                                    ((nb072AlphaDummy042 A B R S_cls H),
                                      (nb072AlphaDummy043 x y H)),
                                    ((nb072AlphaDummy001 A B R S_cls H), y),
                                    ((nb072AlphaDummy000 A B R S_cls H), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072AlphaDummy132 A B R S_cls H) ≠
                                      (nb072AlphaDummy136 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy136;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0132 A B R S_cls H) 0)))) (show
                                    (nb072AlphaDummy134 y H) ≠ (nb072AlphaDummy137 y H)
                                    from (by
                                      unfold nb072AlphaDummy137;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0133 y H)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy132 A B R S_cls H) ≠
                                        (nb072AlphaDummy136 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0132 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy134 y H) ≠
                                        (nb072AlphaDummy137 y H) from (by
                                        unfold nb072AlphaDummy137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0133 y H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb072AlphaDummy136 A B R S_cls H),
                                      (nb072AlphaDummy137 y H)),
                                    ((nb072AlphaDummy132 A B R S_cls H),
                                      (nb072AlphaDummy134 y H)),
                                    ((nb072AlphaDummy133 A B R S_cls H),
                                      (nb072AlphaDummy135 y H)),
                                    ((nb072AlphaDummy125 A B R S_cls H),
                                      (nb072AlphaDummy127 y H)),
                                    ((nb072AlphaDummy124 A B R S_cls H),
                                      (nb072AlphaDummy126 y H)),
                                    ((nb072AlphaDummy130 A B R S_cls H),
                                      (nb072AlphaDummy131 y H)),
                                    ((nb072AlphaDummy128 A B R S_cls H),
                                      (nb072AlphaDummy129 y H)),
                                    ((nb072AlphaDummy116 A B R S_cls H),
                                      (nb072AlphaDummy117 y H)),
                                    ((nb072AlphaDummy118 A B R S_cls H),
                                      (nb072AlphaDummy119 y H)),
                                    ((nb072AlphaDummy121 A B R S_cls H),
                                      (nb072AlphaDummy123 y H)),
                                    ((nb072AlphaDummy120 A B R S_cls H),
                                      (nb072AlphaDummy122 y H)),
                                    ((nb072AlphaDummy039 A B R S_cls H),
                                      (nb072AlphaDummy041 x y H)),
                                    ((nb072AlphaDummy038 A B R S_cls H),
                                      (nb072AlphaDummy040 x y H)),
                                    ((nb072AlphaDummy114 A B R S_cls H),
                                      (nb072AlphaDummy115 x y H)),
                                    ((nb072AlphaDummy042 A B R S_cls H),
                                      (nb072AlphaDummy043 x y H)),
                                    ((nb072AlphaDummy001 A B R S_cls H), y),
                                    ((nb072AlphaDummy000 A B R S_cls H), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                        (nb072AlphaDummy125 A B R S_cls H) from (by
                        unfold nb072AlphaDummy125;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H)
                                1)))) (show y ≠ (nb072AlphaDummy127 y H) from (by
                        unfold nb072AlphaDummy127;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0126 y H) 1))))
                    (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                          (nb072AlphaDummy124 A B R S_cls H) from (by
                          unfold nb072AlphaDummy124;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H)
                                  0)))) (show y ≠ (nb072AlphaDummy126 y H) from (by
                          unfold nb072AlphaDummy126;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))))
                      (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                            (nb072AlphaDummy130 A B R S_cls H) from (by
                            unfold nb072AlphaDummy130;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0128 A B R S_cls H)
                                    0)))) (show y ≠ (nb072AlphaDummy131 y H) from (by
                            unfold nb072AlphaDummy131;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0129 y H) 0))))
                        (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                              (nb072AlphaDummy128 A B R S_cls H) from (by
                              unfold nb072AlphaDummy128;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0125 A B R S_cls H) 0))))
                          (show y ≠ (nb072AlphaDummy129 y H) from (by
                              unfold nb072AlphaDummy129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0127 y H) 0))))
                          (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                                (nb072AlphaDummy116 A B R S_cls H) from (by
                                unfold nb072AlphaDummy116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0118 A B R S_cls H) 0))))
                            (show y ≠ (nb072AlphaDummy117 y H) from (by
                                unfold nb072AlphaDummy117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0121 y H) 0))))
                            (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                                  (nb072AlphaDummy118 A B R S_cls H) from (by
                                  unfold nb072AlphaDummy118;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0119 A B R S_cls H) 0))))
                              (show y ≠ (nb072AlphaDummy119 y H) from (by
                                  unfold nb072AlphaDummy119;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0122 y H)
                                          0)))) (TAlphaVar.there (show
                                  (nb072AlphaDummy001 A B R S_cls H) ≠
                                    (nb072AlphaDummy121 A B R S_cls H) from (by
                                    unfold nb072AlphaDummy121;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb072_support_mem_0120 A B R S_cls H) 1))))
                                (show y ≠ (nb072AlphaDummy123 y H) from (by
                                    unfold nb072AlphaDummy123;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb072_support_mem_0123 y H)
                                            1)))) (TAlphaVar.there (show
                                    (nb072AlphaDummy001 A B R S_cls H) ≠
                                      (nb072AlphaDummy120 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy120;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0120 A B R S_cls H) 0))))
                                  (show y ≠ (nb072AlphaDummy122 y H) from (by
                                      unfold nb072AlphaDummy122;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0123 y H)
                                              0)))) (TAlphaVar.there (show
                                      (nb072AlphaDummy001 A B R S_cls H) ≠
                                        (nb072AlphaDummy039 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy039;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0112 A B R S_cls H)
                                                1))))
                                    (show y ≠ (nb072AlphaDummy041 x y H) from (by
                                        unfold nb072AlphaDummy041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0114 x y H) 1))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy001 A B R S_cls H) ≠
        (nb072AlphaDummy038 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy038;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0112 A B R S_cls H)
                                                  0))))
                                      (show y ≠ (nb072AlphaDummy040 x y H) from (by
                                          unfold nb072AlphaDummy040;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0114 x y H) 0))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy114 A B R S_cls H) from (by
          unfold nb072AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0116 A B R S_cls H)
                  0)))) (show y ≠ (nb072AlphaDummy115 x y H) from (by
          unfold nb072AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0117 x y H) 0)))) (TAlphaVar.there (show
        (nb072AlphaDummy001 A B R S_cls H) ≠ (nb072AlphaDummy042 A B R S_cls H) from (by
          unfold nb072AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0113 A B R S_cls
                    H)
                  0)))) (show y ≠ (nb072AlphaDummy043 x y H) from (by
          unfold nb072AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0115 x y H) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv ∪
                        ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072AlphaDummy125 A B R S_cls H) ≠
                                (nb072AlphaDummy132 A B R S_cls H) from (by
                                unfold nb072AlphaDummy132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0130 A B R S_cls H) 0)))) (show
                              (nb072AlphaDummy127 y H) ≠ (nb072AlphaDummy134 y H) from (by
                                unfold nb072AlphaDummy134;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0131 y H) 0))))
                            (TAlphaVar.there (show (nb072AlphaDummy125 A B R S_cls H) ≠
                                  (nb072AlphaDummy133 A B R S_cls H) from (by
                                  unfold nb072AlphaDummy133;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0130 A B R S_cls H) 1)))) (show
                                (nb072AlphaDummy127 y H) ≠ (nb072AlphaDummy135 y H) from
                                (by
                                  unfold nb072AlphaDummy135;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0131 y H)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb072AlphaDummy125 A B R S_cls H))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb072AlphaDummy127 y H))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy132 A B R S_cls H) ≠ (nb072AlphaDummy139 A B R S_cls H) from (by
          unfold nb072AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0134 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy134 y H) ≠ (nb072AlphaDummy142 y H) from (by
          unfold nb072AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0135 y H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy132 A B R S_cls H) ≠
        (nb072AlphaDummy138 A B R S_cls H) from (by
          unfold nb072AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0134 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy134 y H) ≠ (nb072AlphaDummy141 y H) from (by
          unfold nb072AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0135 y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy132 A B R S_cls H) ≠
        (nb072AlphaDummy136 A B R S_cls H) from (by
          unfold nb072AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0132 A B
                    R S_cls H)
                  0)))) (show (nb072AlphaDummy134 y H) ≠ (nb072AlphaDummy137 y H) from (by
          unfold nb072AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0133 y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy140 A B R S_cls H), (nb072AlphaDummy143 y H)),
        ((nb072AlphaDummy139 A B R S_cls H), (nb072AlphaDummy142 y H)),
        ((nb072AlphaDummy138 A B R S_cls H), (nb072AlphaDummy141 y H)),
        ((nb072AlphaDummy136 A B R S_cls H), (nb072AlphaDummy137 y H)),
        ((nb072AlphaDummy132 A B R S_cls H), (nb072AlphaDummy134 y H)),
        ((nb072AlphaDummy133 A B R S_cls H), (nb072AlphaDummy135 y H)),
        ((nb072AlphaDummy125 A B R S_cls H), (nb072AlphaDummy127 y H)),
        ((nb072AlphaDummy124 A B R S_cls H), (nb072AlphaDummy126 y H)),
        ((nb072AlphaDummy130 A B R S_cls H), (nb072AlphaDummy131 y H)),
        ((nb072AlphaDummy128 A B R S_cls H), (nb072AlphaDummy129 y H)),
        ((nb072AlphaDummy116 A B R S_cls H), (nb072AlphaDummy117 y H)),
        ((nb072AlphaDummy118 A B R S_cls H), (nb072AlphaDummy119 y H)),
        ((nb072AlphaDummy121 A B R S_cls H), (nb072AlphaDummy123 y H)),
        ((nb072AlphaDummy120 A B R S_cls H), (nb072AlphaDummy122 y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠ (nb072AlphaDummy146
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy147 y H) from (by
          unfold
            nb072AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠
        (nb072AlphaDummy144 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy145 y H) from (by
          unfold
            nb072AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠ (nb072AlphaDummy146
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy147 y H) from (by
          unfold
            nb072AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠
        (nb072AlphaDummy144 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy145 y H) from (by
          unfold
            nb072AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠ (nb072AlphaDummy146
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy147 y H) from (by
          unfold
            nb072AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠
        (nb072AlphaDummy144 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy145 y H) from (by
          unfold
            nb072AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠ (nb072AlphaDummy146
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy147 y H) from (by
          unfold
            nb072AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠
        (nb072AlphaDummy144 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy145 y H) from (by
          unfold
            nb072AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy140 A B R S_cls H), (nb072AlphaDummy143 y H)),
        ((nb072AlphaDummy139 A B R S_cls H), (nb072AlphaDummy142 y H)),
        ((nb072AlphaDummy138 A B R S_cls H), (nb072AlphaDummy141 y H)),
        ((nb072AlphaDummy136 A B R S_cls H), (nb072AlphaDummy137 y H)),
        ((nb072AlphaDummy132 A B R S_cls H), (nb072AlphaDummy134 y H)),
        ((nb072AlphaDummy133 A B R S_cls H), (nb072AlphaDummy135 y H)),
        ((nb072AlphaDummy125 A B R S_cls H), (nb072AlphaDummy127 y H)),
        ((nb072AlphaDummy124 A B R S_cls H), (nb072AlphaDummy126 y H)),
        ((nb072AlphaDummy130 A B R S_cls H), (nb072AlphaDummy131 y H)),
        ((nb072AlphaDummy128 A B R S_cls H), (nb072AlphaDummy129 y H)),
        ((nb072AlphaDummy116 A B R S_cls H), (nb072AlphaDummy117 y H)),
        ((nb072AlphaDummy118 A B R S_cls H), (nb072AlphaDummy119 y H)),
        ((nb072AlphaDummy121 A B R S_cls H), (nb072AlphaDummy123 y H)),
        ((nb072AlphaDummy120 A B R S_cls H), (nb072AlphaDummy122 y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132 A B R
        S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy132 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy134 y
        H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠ (nb072AlphaDummy150
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy151 y H) from (by
          unfold
            nb072AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠
        (nb072AlphaDummy148 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy149 y H) from (by
          unfold
            nb072AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠ (nb072AlphaDummy150
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy151 y H) from (by
          unfold
            nb072AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy139 A B R S_cls H) ≠
        (nb072AlphaDummy148 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy142 y H) ≠ (nb072AlphaDummy149 y H) from (by
          unfold
            nb072AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy132
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy134 y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy140
        A B R S_cls H) ≠ (nb072AlphaDummy152 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy153 y H) from (by
          unfold
            nb072AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠
        (nb072AlphaDummy148 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy149 y H) from (by
          unfold
            nb072AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy140
        A B R S_cls H) ≠ (nb072AlphaDummy152 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy153 y H) from (by
          unfold
            nb072AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy140 A B R S_cls H) ≠
        (nb072AlphaDummy148 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy143 y H) ≠ (nb072AlphaDummy149 y H) from (by
          unfold
            nb072AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072AlphaDummy132 A B R S_cls H) ≠
        (nb072AlphaDummy136 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0132 A B R S_cls H)
                                                  0)))) (show (nb072AlphaDummy134 y H) ≠
        (nb072AlphaDummy137 y H) from (by
                                          unfold nb072AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0133 y H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb072AlphaDummy136 A B R S_cls H),
                                        (nb072AlphaDummy137 y H)),
                                      ((nb072AlphaDummy132 A B R S_cls H),
                                        (nb072AlphaDummy134 y H)),
                                      ((nb072AlphaDummy133 A B R S_cls H),
                                        (nb072AlphaDummy135 y H)),
                                      ((nb072AlphaDummy125 A B R S_cls H),
                                        (nb072AlphaDummy127 y H)),
                                      ((nb072AlphaDummy124 A B R S_cls H),
                                        (nb072AlphaDummy126 y H)),
                                      ((nb072AlphaDummy130 A B R S_cls H),
                                        (nb072AlphaDummy131 y H)),
                                      ((nb072AlphaDummy128 A B R S_cls H),
                                        (nb072AlphaDummy129 y H)),
                                      ((nb072AlphaDummy116 A B R S_cls H),
                                        (nb072AlphaDummy117 y H)),
                                      ((nb072AlphaDummy118 A B R S_cls H),
                                        (nb072AlphaDummy119 y H)),
                                      ((nb072AlphaDummy121 A B R S_cls H),
                                        (nb072AlphaDummy123 y H)),
                                      ((nb072AlphaDummy120 A B R S_cls H),
                                        (nb072AlphaDummy122 y H)),
                                      ((nb072AlphaDummy039 A B R S_cls H),
                                        (nb072AlphaDummy041 x y H)),
                                      ((nb072AlphaDummy038 A B R S_cls H),
                                        (nb072AlphaDummy040 x y H)),
                                      ((nb072AlphaDummy114 A B R S_cls H),
                                        (nb072AlphaDummy115 x y H)),
                                      ((nb072AlphaDummy042 A B R S_cls H),
                                        (nb072AlphaDummy043 x y H)),
                                      ((nb072AlphaDummy001 A B R S_cls H), y),
                                      ((nb072AlphaDummy000 A B R S_cls H), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy132 A B R S_cls H) ≠
                                        (nb072AlphaDummy136 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0132 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy134 y H) ≠
                                        (nb072AlphaDummy137 y H) from (by
                                        unfold nb072AlphaDummy137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0133 y H) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072AlphaDummy132 A B R S_cls H) ≠
        (nb072AlphaDummy136 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0132 A B R S_cls H)
                                                  0)))) (show (nb072AlphaDummy134 y H) ≠
        (nb072AlphaDummy137 y H) from (by
                                          unfold nb072AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0133 y H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb072AlphaDummy136 A B R S_cls H),
                                        (nb072AlphaDummy137 y H)),
                                      ((nb072AlphaDummy132 A B R S_cls H),
                                        (nb072AlphaDummy134 y H)),
                                      ((nb072AlphaDummy133 A B R S_cls H),
                                        (nb072AlphaDummy135 y H)),
                                      ((nb072AlphaDummy125 A B R S_cls H),
                                        (nb072AlphaDummy127 y H)),
                                      ((nb072AlphaDummy124 A B R S_cls H),
                                        (nb072AlphaDummy126 y H)),
                                      ((nb072AlphaDummy130 A B R S_cls H),
                                        (nb072AlphaDummy131 y H)),
                                      ((nb072AlphaDummy128 A B R S_cls H),
                                        (nb072AlphaDummy129 y H)),
                                      ((nb072AlphaDummy116 A B R S_cls H),
                                        (nb072AlphaDummy117 y H)),
                                      ((nb072AlphaDummy118 A B R S_cls H),
                                        (nb072AlphaDummy119 y H)),
                                      ((nb072AlphaDummy121 A B R S_cls H),
                                        (nb072AlphaDummy123 y H)),
                                      ((nb072AlphaDummy120 A B R S_cls H),
                                        (nb072AlphaDummy122 y H)),
                                      ((nb072AlphaDummy039 A B R S_cls H),
                                        (nb072AlphaDummy041 x y H)),
                                      ((nb072AlphaDummy038 A B R S_cls H),
                                        (nb072AlphaDummy040 x y H)),
                                      ((nb072AlphaDummy114 A B R S_cls H),
                                        (nb072AlphaDummy115 x y H)),
                                      ((nb072AlphaDummy042 A B R S_cls H),
                                        (nb072AlphaDummy043 x y H)),
                                      ((nb072AlphaDummy001 A B R S_cls H), y),
                                      ((nb072AlphaDummy000 A B R S_cls H), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
