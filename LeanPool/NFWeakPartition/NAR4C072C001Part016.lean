/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C072C001Block004

/-! NF weak partition development: NAR4C072C001Part016. -/


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

/-- Checked nominal proof certificate identified upstream as `nb072_split_alpha_0006`. -/
@[expose]
noncomputable def nb072SplitAlpha0006 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) :
    TAlphaWff
      [((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy039 A B R S_cls H))
          (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))) (Wff.neg
          (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
            (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
              (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy041 x y H)) (synCfv H (Class.cv y)))
        (Wff.neg (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
            (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb072AlphaDummy118 A B R S_cls H) (Wff.classEq
                        (Class.cab (nb072AlphaDummy116 A B R S_cls H)
                          (synWbr (Class.cv (nb072AlphaDummy001 A B R S_cls H)) H
                            (Class.cv (nb072AlphaDummy116 A B R S_cls H))))
                        (synCsn (Class.cv (nb072AlphaDummy118 A B R S_cls H)))))).fv)
                  (by decide)) (freshVar_injective (((Class.cab (nb072AlphaDummy119 y H)
                      (Wff.classEq (Class.cab (nb072AlphaDummy117 y H)
                          (synWbr (Class.cv y) H (Class.cv (nb072AlphaDummy117 y H))))
                        (synCsn (Class.cv (nb072AlphaDummy119 y H)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb072SplitAlpha0004 x y A B R S_cls H)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy116 A B R S_cls H) ≠
        (nb072AlphaDummy125 A B R S_cls H) from (by
          unfold nb072AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0152 A B
                    R S_cls H)
                  1)))) (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy127 y H) from (by
          unfold nb072AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0154 y H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy116 A B R S_cls H) ≠
        (nb072AlphaDummy124 A B R S_cls H) from (by
          unfold nb072AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0152 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy126 y H) from (by
          unfold nb072AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0154 y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy116 A B R S_cls H) ≠
        (nb072AlphaDummy154 A B R S_cls H) from (by
          unfold nb072AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0156
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy155 y H) from (by
          unfold nb072AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0157
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy116 A B R S_cls H) ≠
        (nb072AlphaDummy128 A B R S_cls H) from (by
          unfold nb072AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0153
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy129 y H) from (by
          unfold nb072AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0155
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy001 A B R
        S_cls H))).fv ∪ ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072SplitAlpha0005 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy156 A B R S_cls H), (nb072AlphaDummy157 y H)),
        ((nb072AlphaDummy125 A B R S_cls H), (nb072AlphaDummy127 y H)),
        ((nb072AlphaDummy124 A B R S_cls H), (nb072AlphaDummy126 y H)),
        ((nb072AlphaDummy154 A B R S_cls H), (nb072AlphaDummy155 y H)),
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
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy116 A B R S_cls H) ≠
        (nb072AlphaDummy125 A B R S_cls H) from (by
          unfold nb072AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0152 A B
                    R S_cls H)
                  1)))) (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy127 y H) from (by
          unfold nb072AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0154 y H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy116 A B R S_cls H) ≠
        (nb072AlphaDummy124 A B R S_cls H) from (by
          unfold nb072AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0152 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy126 y H) from (by
          unfold nb072AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0154 y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy116 A B R S_cls H) ≠
        (nb072AlphaDummy154 A B R S_cls H) from (by
          unfold nb072AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0156
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy155 y H) from (by
          unfold nb072AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0157
                    y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy116 A B R S_cls H) ≠
        (nb072AlphaDummy128 A B R S_cls H) from (by
          unfold nb072AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0153
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy117 y H) ≠ (nb072AlphaDummy129 y H) from (by
          unfold nb072AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0155
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy001 A B R
        S_cls H))).fv ∪ ((Class.cv (nb072AlphaDummy116 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv (nb072AlphaDummy117 y H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072SplitAlpha0005 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy156 A B R S_cls H), (nb072AlphaDummy157 y H)),
        ((nb072AlphaDummy125 A B R S_cls H), (nb072AlphaDummy127 y H)),
        ((nb072AlphaDummy124 A B R S_cls H), (nb072AlphaDummy126 y H)),
        ((nb072AlphaDummy154 A B R S_cls H), (nb072AlphaDummy155 y H)),
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
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                        [((nb072AlphaDummy116 A B R S_cls H), (nb072AlphaDummy117 y H)),
                          ((nb072AlphaDummy118 A B R S_cls H), (nb072AlphaDummy119 y H)),
                          ((nb072AlphaDummy121 A B R S_cls H), (nb072AlphaDummy123 y H)),
                          ((nb072AlphaDummy120 A B R S_cls H), (nb072AlphaDummy122 y H)),
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
                        H (nb072FocusedRefl0004 x y A B R S_cls H dv_H_x dv_H_y))))
                  (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there (show
                            (nb072AlphaDummy118 A B R S_cls H) ≠
                              (nb072AlphaDummy160 A B R S_cls H) from (by
                              unfold nb072AlphaDummy160;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0162 A B R S_cls H) 0))))
                          (show (nb072AlphaDummy119 y H) ≠ (nb072AlphaDummy161 y H) from
                            (by
                              unfold nb072AlphaDummy161;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0163 y H) 0))))
                          (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
                ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv) (by decide))
            (freshVar_injective
              (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy039 A B R S_cls H) ≠
                                        (nb072AlphaDummy092 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0090 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy041 x y H) ≠
                                        (nb072AlphaDummy094 x y H) from (by
                                        unfold nb072AlphaDummy094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0091 x y H) 0))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy039 A B R S_cls H) ≠
        (nb072AlphaDummy093 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0090 A B R S_cls H)
                                                  1)))) (show (nb072AlphaDummy041 x y H) ≠
        (nb072AlphaDummy095 x y H) from (by
                                          unfold nb072AlphaDummy095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0091 x y H) 1))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy039 A B R S_cls H) ≠ (nb072AlphaDummy164 A B R S_cls H) from (by
          unfold nb072AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0166 A B R S_cls H)
                  0)))) (show (nb072AlphaDummy041 x y H) ≠ (nb072AlphaDummy165 x y H) from
        (by
          unfold nb072AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0167 x y H) 0)))) (TAlphaVar.there (show
        (nb072AlphaDummy039 A B R S_cls H) ≠ (nb072AlphaDummy162 A B R S_cls H) from (by
          unfold nb072AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0164 A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy041 x y H) ≠ (nb072AlphaDummy163 x y H) from
        (by
          unfold nb072AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0165 x y H) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb072AlphaDummy039 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb072AlphaDummy041 x y H))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy099 A B R S_cls H) from (by
          unfold nb072AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy102 x y H) from
        (by
          unfold nb072AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095
                    x y H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy098 A B R S_cls H) from (by
          unfold nb072AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy101 x y H) from
        (by
          unfold nb072AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy096 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy097 x y H) from
        (by
          unfold
            nb072AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy100 A B R S_cls H), (nb072AlphaDummy103 x y H)),
        ((nb072AlphaDummy099 A B R S_cls H), (nb072AlphaDummy102 x y H)),
        ((nb072AlphaDummy098 A B R S_cls H), (nb072AlphaDummy101 x y H)),
        ((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy164 A B R S_cls H), (nb072AlphaDummy165 x y H)),
        ((nb072AlphaDummy162 A B R S_cls H), (nb072AlphaDummy163 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
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
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy100
        A B R S_cls H) ≠ (nb072AlphaDummy106 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A
                    B
                    R
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
                    x
                    y
                    H)
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
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy100
        A B R S_cls H) ≠ (nb072AlphaDummy106 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy100 A B R S_cls H), (nb072AlphaDummy103 x y H)),
        ((nb072AlphaDummy099 A B R S_cls H), (nb072AlphaDummy102 x y H)),
        ((nb072AlphaDummy098 A B R S_cls H), (nb072AlphaDummy101 x y H)),
        ((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy164 A B R S_cls H), (nb072AlphaDummy165 x y H)),
        ((nb072AlphaDummy162 A B R S_cls H), (nb072AlphaDummy163 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092 A B R S_cls
        H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094
        x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
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
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy111 x y H) from
        (by
          unfold
            nb072AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy099
        A B R S_cls H) ≠ (nb072AlphaDummy110 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy111 x y H) from
        (by
          unfold
            nb072AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠ (nb072AlphaDummy112
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy113 x y H) from
        (by
          unfold
            nb072AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A
                    B
                    R
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
                    x
                    y
                    H)
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
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy113 x y H) from
        (by
          unfold
            nb072AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
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
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy164 A B R S_cls H), (nb072AlphaDummy165 x y H)),
        ((nb072AlphaDummy162 A B R S_cls H), (nb072AlphaDummy163 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
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
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy164 A B R S_cls H), (nb072AlphaDummy165 x y H)),
        ((nb072AlphaDummy162 A B R S_cls H), (nb072AlphaDummy163 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy039 A B R S_cls H) ≠
                                        (nb072AlphaDummy092 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0090 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy041 x y H) ≠
                                        (nb072AlphaDummy094 x y H) from (by
                                        unfold nb072AlphaDummy094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0091 x y H) 0))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy039 A B R S_cls H) ≠
        (nb072AlphaDummy093 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0090 A B R S_cls H)
                                                  1)))) (show (nb072AlphaDummy041 x y H) ≠
        (nb072AlphaDummy095 x y H) from (by
                                          unfold nb072AlphaDummy095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0091 x y H) 1))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy039 A B R S_cls H) ≠ (nb072AlphaDummy164 A B R S_cls H) from (by
          unfold nb072AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0166 A B R S_cls H)
                  0)))) (show (nb072AlphaDummy041 x y H) ≠ (nb072AlphaDummy165 x y H) from
        (by
          unfold nb072AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0167 x y H) 0)))) (TAlphaVar.there (show
        (nb072AlphaDummy039 A B R S_cls H) ≠ (nb072AlphaDummy162 A B R S_cls H) from (by
          unfold nb072AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0164 A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy041 x y H) ≠ (nb072AlphaDummy163 x y H) from
        (by
          unfold nb072AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0165 x y H) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb072AlphaDummy039 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb072AlphaDummy041 x y H))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy099 A B R S_cls H) from (by
          unfold nb072AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy102 x y H) from
        (by
          unfold nb072AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095
                    x y H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy098 A B R S_cls H) from (by
          unfold nb072AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy101 x y H) from
        (by
          unfold nb072AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
        (nb072AlphaDummy096 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy094 x y H) ≠ (nb072AlphaDummy097 x y H) from
        (by
          unfold
            nb072AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy100 A B R S_cls H), (nb072AlphaDummy103 x y H)),
        ((nb072AlphaDummy099 A B R S_cls H), (nb072AlphaDummy102 x y H)),
        ((nb072AlphaDummy098 A B R S_cls H), (nb072AlphaDummy101 x y H)),
        ((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy164 A B R S_cls H), (nb072AlphaDummy165 x y H)),
        ((nb072AlphaDummy162 A B R S_cls H), (nb072AlphaDummy163 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
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
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy100
        A B R S_cls H) ≠ (nb072AlphaDummy106 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A
                    B
                    R
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
                    x
                    y
                    H)
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
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy100
        A B R S_cls H) ≠ (nb072AlphaDummy106 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy107 x y H) from
        (by
          unfold
            nb072AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy104 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy100 A B R S_cls H), (nb072AlphaDummy103 x y H)),
        ((nb072AlphaDummy099 A B R S_cls H), (nb072AlphaDummy102 x y H)),
        ((nb072AlphaDummy098 A B R S_cls H), (nb072AlphaDummy101 x y H)),
        ((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy164 A B R S_cls H), (nb072AlphaDummy165 x y H)),
        ((nb072AlphaDummy162 A B R S_cls H), (nb072AlphaDummy163 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092 A B R S_cls
        H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy094 x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy092 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094
        x y H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
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
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy111 x y H) from
        (by
          unfold
            nb072AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy099
        A B R S_cls H) ≠ (nb072AlphaDummy110 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy102 x y H) ≠ (nb072AlphaDummy111 x y H) from
        (by
          unfold
            nb072AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy099 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy092
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy094 x y H))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠ (nb072AlphaDummy112
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy113 x y H) from
        (by
          unfold
            nb072AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A
                    B
                    R
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
                    x
                    y
                    H)
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
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy103 x y H) ≠ (nb072AlphaDummy113 x y H) from
        (by
          unfold
            nb072AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy100 A B R S_cls H) ≠
        (nb072AlphaDummy108 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A
                    B
                    R
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
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
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
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy164 A B R S_cls H), (nb072AlphaDummy165 x y H)),
        ((nb072AlphaDummy162 A B R S_cls H), (nb072AlphaDummy163 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy092 A B R S_cls H) ≠
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
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy096 A B R S_cls H), (nb072AlphaDummy097 x y H)),
        ((nb072AlphaDummy092 A B R S_cls H), (nb072AlphaDummy094 x y H)),
        ((nb072AlphaDummy093 A B R S_cls H), (nb072AlphaDummy095 x y H)),
        ((nb072AlphaDummy164 A B R S_cls H), (nb072AlphaDummy165 x y H)),
        ((nb072AlphaDummy162 A B R S_cls H), (nb072AlphaDummy163 x y H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb072AlphaDummy162 A B R S_cls H), (nb072AlphaDummy163 x y H)),
                    ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
                    ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
                    ((nb072AlphaDummy114 A B R S_cls H), (nb072AlphaDummy115 x y H)),
                    ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
                    ((nb072AlphaDummy001 A B R S_cls H), y),
                    ((nb072AlphaDummy000 A B R S_cls H), x)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb072_focused_notmem_0032 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy001 A B R S_cls H) ∉ S_cls.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb072_focused_notmem_0033 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy000 A B R S_cls H) ∉ S_cls.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb072_compact_envfresh_0034 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) :
    TEnvFresh
      [((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      S_cls.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb072AlphaDummy001 A B R S_cls H) y
      (nb072_focused_notmem_0032 A B R S_cls H) dv_S_y
      (TEnvFresh.consFresh (nb072AlphaDummy000 A B R S_cls H) x
        (nb072_focused_notmem_0033 A B R S_cls H) dv_S_x (TEnvFresh.nil S_cls.fv)))

/-- Checked nominal proof certificate identified upstream as `nb072_focused_refl_0005`. -/
@[expose]
noncomputable def nb072FocusedRefl0005 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) :
    TReflOn
      [((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      S_cls.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0034 x y A B R S_cls H dv_S_x dv_S_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
