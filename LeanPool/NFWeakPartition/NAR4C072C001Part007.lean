/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C072C001Block001

/-! NF weak partition development: NAR4C072C001Part007. -/


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

/-- Checked nominal proof certificate identified upstream as `nb072_split_alpha_0000`. -/
@[expose]
noncomputable def nb072SplitAlpha0000 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) :
    TAlphaWff
      [((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy032 A B R S_cls H))
          (Class.cab (nb072AlphaDummy002 A B R S_cls H)
            (synWrex (nb072AlphaDummy003 A B R S_cls H)
              (Class.cv (nb072AlphaDummy001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy032 A B R S_cls H))
            (Class.cab (nb072AlphaDummy002 A B R S_cls H)
              (synWrex (nb072AlphaDummy003 A B R S_cls H)
                (Class.cv (nb072AlphaDummy001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy002 A B R S_cls H))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy003 A B R S_cls H)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy033 x y))
          (Class.cab (nb072AlphaDummy004 x y)
            (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy033 x y))
            (Class.cab (nb072AlphaDummy004 x y)
              (synWrex (nb072AlphaDummy005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072AlphaDummy004 x y))
                  (synCun (synCphi (Class.cv (nb072AlphaDummy005 x y)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                      (nb072AlphaDummy003 A B R S_cls H) from (by
                      unfold nb072AlphaDummy003;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 1))))
                  (show y ≠ (nb072AlphaDummy005 x y) from (by
                      unfold nb072AlphaDummy005;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0030 x y) 1)))) (TAlphaVar.there
                    (show (nb072AlphaDummy001 A B R S_cls H) ≠
                        (nb072AlphaDummy002 A B R S_cls H) from (by
                        unfold nb072AlphaDummy002;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H)
                                0)))) (show y ≠ (nb072AlphaDummy004 x y) from (by
                        unfold nb072AlphaDummy004;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))))
                    (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                          (nb072AlphaDummy032 A B R S_cls H) from (by
                          unfold nb072AlphaDummy032;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0032 A B R S_cls H)
                                  0)))) (show y ≠ (nb072AlphaDummy033 x y) from (by
                          unfold nb072AlphaDummy033;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0033 x y) 0))))
                      (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                            (nb072AlphaDummy006 A B R S_cls H) from (by
                            unfold nb072AlphaDummy006;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0029 A B R S_cls H)
                                    0)))) (show y ≠ (nb072AlphaDummy007 x y) from (by
                            unfold nb072AlphaDummy007;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0031 x y) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
                      ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy036 A B R S_cls H) from (by
          unfold nb072AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0036 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy037 x y) from (by
          unfold nb072AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0037 x y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy003 A B R S_cls H) ≠
        (nb072AlphaDummy034 A B R S_cls H) from (by
          unfold nb072AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0034 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy035 x y) from (by
          unfold nb072AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0035 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb072AlphaDummy003 A B R S_cls H))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb072AlphaDummy005 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.there (show
        (nb072AlphaDummy003 A B R S_cls H) ≠ (nb072AlphaDummy036 A B R S_cls H) from (by
          unfold nb072AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0036 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy037 x y) from (by
          unfold nb072AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0037 x y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy003 A B R S_cls H) ≠
        (nb072AlphaDummy034 A B R S_cls H) from (by
          unfold nb072AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0034 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy035 x y) from (by
          unfold nb072AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0035 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb072AlphaDummy003 A B R S_cls H))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb072AlphaDummy005 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed [((nb072AlphaDummy034 A B R S_cls H),
                            (nb072AlphaDummy035 x y)),
                          ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
                          ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
                          ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
                          ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
                          ((nb072AlphaDummy001 A B R S_cls H), y),
                          ((nb072AlphaDummy000 A B R S_cls H), x)]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                        (nb072AlphaDummy003 A B R S_cls H) from (by
                        unfold nb072AlphaDummy003;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H)
                                1)))) (show y ≠ (nb072AlphaDummy005 x y) from (by
                        unfold nb072AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0030 x y) 1))))
                    (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                          (nb072AlphaDummy002 A B R S_cls H) from (by
                          unfold nb072AlphaDummy002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H)
                                  0)))) (show y ≠ (nb072AlphaDummy004 x y) from (by
                          unfold nb072AlphaDummy004;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))))
                      (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                            (nb072AlphaDummy032 A B R S_cls H) from (by
                            unfold nb072AlphaDummy032;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0032 A B R S_cls H)
                                    0)))) (show y ≠ (nb072AlphaDummy033 x y) from (by
                            unfold nb072AlphaDummy033;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0033 x y) 0))))
                        (TAlphaVar.there (show (nb072AlphaDummy001 A B R S_cls H) ≠
                              (nb072AlphaDummy006 A B R S_cls H) from (by
                              unfold nb072AlphaDummy006;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0029 A B R S_cls H) 0))))
                          (show y ≠ (nb072AlphaDummy007 x y) from (by
                              unfold nb072AlphaDummy007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0031 x y) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
                        ((Class.cv (nb072AlphaDummy001 A B R S_cls H))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy003 A B R S_cls H) ≠
        (nb072AlphaDummy010 A B R S_cls H) from (by
          unfold nb072AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
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
                  (nb072_support_mem_0007 x y)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy003 A B R S_cls H) ≠
        (nb072AlphaDummy036 A B R S_cls H) from (by
          unfold nb072AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0036 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy037 x y) from (by
          unfold nb072AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0037 x y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy003 A B R S_cls H) ≠
        (nb072AlphaDummy034 A B R S_cls H) from (by
          unfold nb072AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0034 A B
                    R S_cls H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy035 x y) from (by
          unfold nb072AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0035 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy003 A B R S_cls
        H))).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy005 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    A B R S_cls
                    H)
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
                    A B R
                    S_cls H)
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
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
                  (nb072_support_mem_0008
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy003 A B R S_cls H) ≠
        (nb072AlphaDummy010 A B R S_cls H) from (by
          unfold nb072AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
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
                  (nb072_support_mem_0007 x y)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy003 A B R S_cls H) ≠
        (nb072AlphaDummy036 A B R S_cls H) from (by
          unfold nb072AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0036 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy037 x y) from (by
          unfold nb072AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0037 x y)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy003 A B R S_cls H) ≠
        (nb072AlphaDummy034 A B R S_cls H) from (by
          unfold nb072AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0034 A B
                    R S_cls H)
                  0)))) (show (nb072AlphaDummy005 x y) ≠ (nb072AlphaDummy035 x y) from (by
          unfold nb072AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0035 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy003 A B R S_cls
        H))).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy005 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    A B R S_cls
                    H)
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
                    A B R
                    S_cls H)
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy017 A B R S_cls H) ≠
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
                  (nb072_support_mem_0008
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy010 A B R S_cls H) ≠
        (nb072AlphaDummy014 A B R S_cls H) from (by
          unfold nb072AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy012 x y) ≠ (nb072AlphaDummy015 x y) from (by
          unfold nb072AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy014 A B R S_cls H), (nb072AlphaDummy015 x y)),
        ((nb072AlphaDummy010 A B R S_cls H), (nb072AlphaDummy012 x y)),
        ((nb072AlphaDummy011 A B R S_cls H), (nb072AlphaDummy013 x y)),
        ((nb072AlphaDummy036 A B R S_cls H), (nb072AlphaDummy037 x y)),
        ((nb072AlphaDummy034 A B R S_cls H), (nb072AlphaDummy035 x y)),
        ((nb072AlphaDummy003 A B R S_cls H), (nb072AlphaDummy005 x y)),
        ((nb072AlphaDummy002 A B R S_cls H), (nb072AlphaDummy004 x y)),
        ((nb072AlphaDummy032 A B R S_cls H), (nb072AlphaDummy033 x y)),
        ((nb072AlphaDummy006 A B R S_cls H), (nb072AlphaDummy007 x y)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed [((nb072AlphaDummy034 A B R S_cls H),
                              (nb072AlphaDummy035 x y)),
                            ((nb072AlphaDummy003 A B R S_cls H),
                              (nb072AlphaDummy005 x y)),
                            ((nb072AlphaDummy002 A B R S_cls H),
                              (nb072AlphaDummy004 x y)),
                            ((nb072AlphaDummy032 A B R S_cls H),
                              (nb072AlphaDummy033 x y)),
                            ((nb072AlphaDummy006 A B R S_cls H),
                              (nb072AlphaDummy007 x y)),
                            ((nb072AlphaDummy001 A B R S_cls H), y),
                            ((nb072AlphaDummy000 A B R S_cls H), x)]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb072_focused_notmem_0002 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy001 A B R S_cls H) ∉ R.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))))

theorem nb072_focused_notmem_0003 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy000 A B R S_cls H) ∉ R.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))))

theorem nb072_compact_envfresh_0010 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TEnvFresh
      [((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb072AlphaDummy001 A B R S_cls H) y
      (nb072_focused_notmem_0002 A B R S_cls H) dv_R_y
      (TEnvFresh.consFresh (nb072AlphaDummy000 A B R S_cls H) x
        (nb072_focused_notmem_0003 A B R S_cls H) dv_R_x (TEnvFresh.nil R.fv)))

/-- Checked nominal proof certificate identified upstream as `nb072_focused_refl_0002`. -/
@[expose]
noncomputable def nb072FocusedRefl0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TReflOn
      [((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      R.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0010 x y A B R S_cls H dv_R_x dv_R_y)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
