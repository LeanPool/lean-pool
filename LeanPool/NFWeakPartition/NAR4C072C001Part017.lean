/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C072C001Part016

/-! NF weak partition development: NAR4C072C001Part017. -/


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

/-- Checked nominal proof certificate identified upstream as `nb072_split_alpha_0007`. -/
@[expose]
noncomputable def nb072SplitAlpha0007 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      (Wff.imp (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) R
          (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
        (synWbr (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H))) S_cls
          (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))))
      (Wff.imp (synWbr (Class.cv x) R (Class.cv y))
        (synWbr (synCfv H (Class.cv x)) S_cls (synCfv H (Class.cv y)))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072AlphaDummy000 A B R S_cls H) ≠
                                      (nb072AlphaDummy003 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0000 A B R S_cls H) 1))))
                                  (show x ≠ (nb072AlphaDummy005 x y) from (by
                                      unfold nb072AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0002 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb072AlphaDummy000 A B R S_cls H) ≠
                                        (nb072AlphaDummy002 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0000 A B R S_cls H)
                                                0)))) (show x ≠ (nb072AlphaDummy004 x y) from
                                      (by
                                        unfold nb072AlphaDummy004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0002 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy000 A B R S_cls H) ≠
        (nb072AlphaDummy008 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy008;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0004 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072AlphaDummy009 x y) from (by
                                          unfold nb072AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0005 x y) 0))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy006 A B R S_cls H) from (by
          unfold nb072AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0001 A B R S_cls H)
                  0)))) (show x ≠ (nb072AlphaDummy007 x y) from (by
          unfold nb072AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0003 x y) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv
        (nb072AlphaDummy000 A B R S_cls H))).fv ∪ ((Class.cv
        (nb072AlphaDummy001 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy010 A B R S_cls H) from (by
          unfold nb072AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy012 x y) from (by
          unfold nb072AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy011 A B R S_cls H) from (by
          unfold nb072AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy013 x y) from (by
          unfold nb072AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072AlphaDummy005 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy010 A B R S_cls H) ≠ (nb072AlphaDummy017 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy020 x y) from (by
          unfold
            nb072AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy016 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy019 x y) from (by
          unfold
            nb072AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold
            nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy018 A B R S_cls H), (nb072AlphaDummy021 x y)),
        ((nb072AlphaDummy017 A B R S_cls H), (nb072AlphaDummy020 x y)),
        ((nb072AlphaDummy016 A B R S_cls H), (nb072AlphaDummy019 x y)),
        ((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy017 A B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠ (nb072AlphaDummy024 A
        B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy018 A B R S_cls H), (nb072AlphaDummy021 x y)),
        ((nb072AlphaDummy017 A B R S_cls H), (nb072AlphaDummy020 x y)),
        ((nb072AlphaDummy016 A B R S_cls H), (nb072AlphaDummy019 x y)),
        ((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012
        x y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy028 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy029 x y) from (by
          unfold
            nb072AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A
        B R S_cls H) ≠ (nb072AlphaDummy028 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy029 x y) from (by
          unfold
            nb072AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠ (nb072AlphaDummy030 A
        B R S_cls H) from (by
          unfold
            nb072AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy031 x y) from (by
          unfold
            nb072AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy030 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy031 x y) from (by
          unfold
            nb072AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy010 A B R S_cls H) ≠ (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A B
                    R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072AlphaDummy000 A B R S_cls H) ≠
                                      (nb072AlphaDummy003 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0000 A B R S_cls H) 1))))
                                  (show x ≠ (nb072AlphaDummy005 x y) from (by
                                      unfold nb072AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0002 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb072AlphaDummy000 A B R S_cls H) ≠
                                        (nb072AlphaDummy002 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0000 A B R S_cls H)
                                                0)))) (show x ≠ (nb072AlphaDummy004 x y) from
                                      (by
                                        unfold nb072AlphaDummy004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0002 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy000 A B R S_cls H) ≠
        (nb072AlphaDummy008 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy008;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0004 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072AlphaDummy009 x y) from (by
                                          unfold nb072AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0005 x y) 0))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy006 A B R S_cls H) from (by
          unfold nb072AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0001 A B R S_cls H)
                  0)))) (show x ≠ (nb072AlphaDummy007 x y) from (by
          unfold nb072AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0003 x y) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv
        (nb072AlphaDummy000 A B R S_cls H))).fv ∪ ((Class.cv
        (nb072AlphaDummy001 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy010 A B R S_cls H) from (by
          unfold nb072AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy012 x y) from (by
          unfold nb072AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy011 A B R S_cls H) from (by
          unfold nb072AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy013 x y) from (by
          unfold nb072AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072AlphaDummy005 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy010 A B R S_cls H) ≠ (nb072AlphaDummy017 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy020 x y) from (by
          unfold
            nb072AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy016 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy019 x y) from (by
          unfold
            nb072AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold
            nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy018 A B R S_cls H), (nb072AlphaDummy021 x y)),
        ((nb072AlphaDummy017 A B R S_cls H), (nb072AlphaDummy020 x y)),
        ((nb072AlphaDummy016 A B R S_cls H), (nb072AlphaDummy019 x y)),
        ((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy017 A B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠ (nb072AlphaDummy024 A
        B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy018 A B R S_cls H), (nb072AlphaDummy021 x y)),
        ((nb072AlphaDummy017 A B R S_cls H), (nb072AlphaDummy020 x y)),
        ((nb072AlphaDummy016 A B R S_cls H), (nb072AlphaDummy019 x y)),
        ((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012
        x y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy028 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy029 x y) from (by
          unfold
            nb072AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A
        B R S_cls H) ≠ (nb072AlphaDummy028 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy029 x y) from (by
          unfold
            nb072AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠ (nb072AlphaDummy030 A
        B R S_cls H) from (by
          unfold
            nb072AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy031 x y) from (by
          unfold
            nb072AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy030 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy031 x y) from (by
          unfold
            nb072AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy010 A B R S_cls H) ≠ (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A B
                    R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb072SplitAlpha0000 x y A B R S_cls H))))))))
      (TAlphaClass.reflOfReflOn [((nb072AlphaDummy001 A B R S_cls H), y),
          ((nb072AlphaDummy000 A B R S_cls H), x)]
        R (nb072FocusedRefl0002 x y A B R S_cls H dv_R_x dv_R_y))) (TAlphaWff.classMem
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg
                    (nb072SplitAlpha0003 x y A B R S_cls H dv_H_x dv_H_y dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb072SplitAlpha0006 x y A B R S_cls H dv_H_x dv_H_y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb072SplitAlpha0006 x y A B R S_cls H dv_H_x dv_H_y))))))))))))
      (TAlphaClass.reflOfReflOn [((nb072AlphaDummy001 A B R S_cls H), y),
          ((nb072AlphaDummy000 A B R S_cls H), x)]
        S_cls (nb072FocusedRefl0005 x y A B R S_cls H dv_S_x dv_S_y))))

/-- Checked nominal proof certificate identified upstream as `nb072_split_alpha_0008`. -/
@[expose]
noncomputable def nb072SplitAlpha0008 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      (Wff.imp (synWbr (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H))) S_cls
          (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H))))
        (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) R
          (Class.cv (nb072AlphaDummy001 A B R S_cls H))))
      (Wff.imp (synWbr (synCfv H (Class.cv x)) S_cls (synCfv H (Class.cv y)))
        (synWbr (Class.cv x) R (Class.cv y))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg
                    (nb072SplitAlpha0003 x y A B R S_cls H dv_H_x dv_H_y dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb072SplitAlpha0006 x y A B R S_cls H dv_H_x dv_H_y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb072SplitAlpha0006 x y A B R S_cls H dv_H_x dv_H_y))))))))))))
      (TAlphaClass.reflOfReflOn [((nb072AlphaDummy001 A B R S_cls H), y),
          ((nb072AlphaDummy000 A B R S_cls H), x)]
        S_cls (nb072FocusedRefl0005 x y A B R S_cls H dv_S_x dv_S_y))) (TAlphaWff.classMem
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072AlphaDummy000 A B R S_cls H) ≠
                                      (nb072AlphaDummy003 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0000 A B R S_cls H) 1))))
                                  (show x ≠ (nb072AlphaDummy005 x y) from (by
                                      unfold nb072AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0002 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb072AlphaDummy000 A B R S_cls H) ≠
                                        (nb072AlphaDummy002 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0000 A B R S_cls H)
                                                0)))) (show x ≠ (nb072AlphaDummy004 x y) from
                                      (by
                                        unfold nb072AlphaDummy004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0002 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy000 A B R S_cls H) ≠
        (nb072AlphaDummy008 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy008;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0004 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072AlphaDummy009 x y) from (by
                                          unfold nb072AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0005 x y) 0))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy006 A B R S_cls H) from (by
          unfold nb072AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0001 A B R S_cls H)
                  0)))) (show x ≠ (nb072AlphaDummy007 x y) from (by
          unfold nb072AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0003 x y) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv
        (nb072AlphaDummy000 A B R S_cls H))).fv ∪ ((Class.cv
        (nb072AlphaDummy001 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy010 A B R S_cls H) from (by
          unfold nb072AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy012 x y) from (by
          unfold nb072AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy011 A B R S_cls H) from (by
          unfold nb072AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy013 x y) from (by
          unfold nb072AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072AlphaDummy005 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy010 A B R S_cls H) ≠ (nb072AlphaDummy017 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy020 x y) from (by
          unfold
            nb072AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy016 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy019 x y) from (by
          unfold
            nb072AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold
            nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy018 A B R S_cls H), (nb072AlphaDummy021 x y)),
        ((nb072AlphaDummy017 A B R S_cls H), (nb072AlphaDummy020 x y)),
        ((nb072AlphaDummy016 A B R S_cls H), (nb072AlphaDummy019 x y)),
        ((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy017 A B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠ (nb072AlphaDummy024 A
        B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy018 A B R S_cls H), (nb072AlphaDummy021 x y)),
        ((nb072AlphaDummy017 A B R S_cls H), (nb072AlphaDummy020 x y)),
        ((nb072AlphaDummy016 A B R S_cls H), (nb072AlphaDummy019 x y)),
        ((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012
        x y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy028 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy029 x y) from (by
          unfold
            nb072AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A
        B R S_cls H) ≠ (nb072AlphaDummy028 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy029 x y) from (by
          unfold
            nb072AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠ (nb072AlphaDummy030 A
        B R S_cls H) from (by
          unfold
            nb072AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy031 x y) from (by
          unfold
            nb072AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy030 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy031 x y) from (by
          unfold
            nb072AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy010 A B R S_cls H) ≠ (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A B
                    R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072AlphaDummy000 A B R S_cls H) ≠
                                      (nb072AlphaDummy003 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0000 A B R S_cls H) 1))))
                                  (show x ≠ (nb072AlphaDummy005 x y) from (by
                                      unfold nb072AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0002 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb072AlphaDummy000 A B R S_cls H) ≠
                                        (nb072AlphaDummy002 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0000 A B R S_cls H)
                                                0)))) (show x ≠ (nb072AlphaDummy004 x y) from
                                      (by
                                        unfold nb072AlphaDummy004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0002 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy000 A B R S_cls H) ≠
        (nb072AlphaDummy008 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy008;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0004 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072AlphaDummy009 x y) from (by
                                          unfold nb072AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0005 x y) 0))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy006 A B R S_cls H) from (by
          unfold nb072AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0001 A B R S_cls H)
                  0)))) (show x ≠ (nb072AlphaDummy007 x y) from (by
          unfold nb072AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0003 x y) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv
        (nb072AlphaDummy000 A B R S_cls H))).fv ∪ ((Class.cv
        (nb072AlphaDummy001 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy010 A B R S_cls H) from (by
          unfold nb072AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy012 x y) from (by
          unfold nb072AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy011 A B R S_cls H) from (by
          unfold nb072AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy013 x y) from (by
          unfold nb072AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy003 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072AlphaDummy005 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy010 A B R S_cls H) ≠ (nb072AlphaDummy017 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  1)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy020 x y) from (by
          unfold
            nb072AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy016 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy019 x y) from (by
          unfold
            nb072AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold
            nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy018 A B R S_cls H), (nb072AlphaDummy021 x y)),
        ((nb072AlphaDummy017 A B R S_cls H), (nb072AlphaDummy020 x y)),
        ((nb072AlphaDummy016 A B R S_cls H), (nb072AlphaDummy019 x y)),
        ((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy017 A B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠ (nb072AlphaDummy024 A
        B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy024 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy025 x y) from (by
          unfold
            nb072AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy022 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy023 x y) from (by
          unfold
            nb072AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy018 A B R S_cls H), (nb072AlphaDummy021 x y)),
        ((nb072AlphaDummy017 A B R S_cls H), (nb072AlphaDummy020 x y)),
        ((nb072AlphaDummy016 A B R S_cls H), (nb072AlphaDummy019 x y)),
        ((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012
        x y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb072AlphaDummy010 A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy028 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy029 x y) from (by
          unfold
            nb072AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A
        B R S_cls H) ≠ (nb072AlphaDummy028 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy029 x y) from (by
          unfold
            nb072AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy020 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy010
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy012 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠ (nb072AlphaDummy030 A
        B R S_cls H) from (by
          unfold
            nb072AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy031 x y) from (by
          unfold
            nb072AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy018 A
        B R S_cls H) ≠ (nb072AlphaDummy030 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy031 x y) from (by
          unfold
            nb072AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy018 A B R S_cls H) ≠
        (nb072AlphaDummy026 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy021 x y) ≠ (nb072AlphaDummy027 x y) from (by
          unfold
            nb072AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy010 A B R S_cls H) ≠ (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A B
                    R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy008 A B R S_cls H), (nb072AlphaDummy009 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb072SplitAlpha0000 x y A B R S_cls H))))))))
      (TAlphaClass.reflOfReflOn [((nb072AlphaDummy001 A B R S_cls H), y),
          ((nb072AlphaDummy000 A B R S_cls H), x)]
        R (nb072FocusedRefl0002 x y A B R S_cls H dv_R_x dv_R_y))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_iso`. -/
@[expose]
noncomputable def nominalDfIso (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (__dv_B_x : x ∉ B.fv) (__dv_B_y : y ∉ B.fv) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWiso H R S_cls A B) (synWa (synWf1o H A B) (synWral x A (synWral y A
              (synWb (synWbr (.cv x) R (.cv y))
                (synWbr (synCfv H (.cv x)) S_cls (synCfv H (.cv y)))))))) :=
  by
  change
    Nominal.NPrf
      (Wff.biimp (synWiso H R S_cls A B) (synWa (synWf1o H A B) (synWral x A (synWral y A
              (synWb (synWbr (Class.cv x) R (Class.cv y))
                (synWbr (synCfv H (Class.cv x)) S_cls (synCfv H (Class.cv y))))))))
  exact
    Nominal.alphaBiimp
      (TAlphaWff.conj (TAlphaWff.reflOfReflOn [] (synWf1o H A B) (nb072WppRefl0000 A B H))
        (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn [((nb072AlphaDummy000 A B R S_cls H), x)] A
                (nb072FocusedRefl0000 x A B R S_cls H dv_A_x))) (TAlphaWff.all (TAlphaWff.imp
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfReflOn [((nb072AlphaDummy001 A B R S_cls H), y),
                      ((nb072AlphaDummy000 A B R S_cls H), x)]
                    A (nb072FocusedRefl0001 x y A B R S_cls H dv_A_x dv_A_y)))
                (TAlphaWff.conj
                  (nb072SplitAlpha0007 x y A B R S_cls H dv_H_x dv_H_y dv_R_x dv_R_y
                    dv_S_x dv_S_y dv_x_y)
                  (nb072SplitAlpha0008 x y A B R S_cls H dv_H_x dv_H_y dv_R_x dv_R_y
                    dv_S_x dv_S_y dv_x_y)))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
