/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C081C001Part004

/-! NF weak partition development: NAR4C081C001Part005. -/


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

/-- Checked nominal proof certificate identified upstream as `nb081_split_alpha_0001`. -/
@[expose]
noncomputable def nb081SplitAlpha0001 (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))]
      (Wff.imp (Wff.classEq (Class.cv (nb081AlphaDummy002 A))
          (synCop (Class.cv (nb081AlphaDummy000 A)) (Class.cv (nb081AlphaDummy001 A))))
        (Wff.neg (Wff.classMem (synCopk (Class.cv (nb081AlphaDummy000 A))
              (Class.cv (nb081AlphaDummy001 A))) A)))
      (Wff.imp (Wff.classEq (Class.cv (nb081AlphaDummy003 x y A))
          (synCop (Class.cv x) (Class.cv y)))
        (Wff.neg (Wff.classMem (synCopk (Class.cv x) (Class.cv y)) A))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy002 A) from (by
                unfold nb081AlphaDummy002;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0002 A) 0)))))
          (Ne.symm (show y ≠ (nb081AlphaDummy003 x y A) from (by
                unfold nb081AlphaDummy003;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0003 x y A) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy002 A) from (by
                  unfold nb081AlphaDummy002;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0000 A) 0)))))
            (Ne.symm (show x ≠ (nb081AlphaDummy003 x y A) from (by
                  unfold nb081AlphaDummy003;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0001 x y A) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy005 A) from
                                    (by
                                      unfold nb081AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb081_support_mem_0004 A)
                                              1)))) (show x ≠ (nb081AlphaDummy007 x y) from
                                    (by
                                      unfold nb081AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb081_support_mem_0006 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy004 A) from
                                      (by
                                        unfold nb081AlphaDummy004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0004 A)
                                                0)))) (show x ≠ (nb081AlphaDummy006 x y) from
                                      (by
                                        unfold nb081AlphaDummy006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb081_support_mem_0006 x y) 0))))
                                    (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy010 A) from (by
                                          unfold nb081AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0008 A) 0))))
                                      (show x ≠ (nb081AlphaDummy011 x y) from (by
                                          unfold nb081AlphaDummy011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0009 x y) 0))))
                                      (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy008 A) from (by
          unfold nb081AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0005 A) 0)))) (show x ≠ (nb081AlphaDummy009 x y) from
        (by
          unfold nb081AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb081AlphaDummy000 A))).fv ∪
                                      ((Class.cv (nb081AlphaDummy001 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy012 A) from (by
          unfold nb081AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy014 x y) from (by
          unfold nb081AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy013 A) from (by
          unfold nb081AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy015 x y) from (by
          unfold nb081AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081AlphaDummy005 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb081AlphaDummy007 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy019 A) from (by
          unfold
            nb081AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy022 x y) from (by
          unfold
            nb081AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy018 A) from (by
          unfold
            nb081AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy021 x y) from (by
          unfold
            nb081AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold
            nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold
            nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)), ((nb081AlphaDummy004 A),
        (nb081AlphaDummy006 x y)), ((nb081AlphaDummy010 A), (nb081AlphaDummy011 x y)),
        ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)), ((nb081AlphaDummy001 A),
        y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x
        y A))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)), ((nb081AlphaDummy004 A),
        (nb081AlphaDummy006 x y)), ((nb081AlphaDummy010 A), (nb081AlphaDummy011 x y)),
        ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)), ((nb081AlphaDummy001 A),
        y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002 A), (nb081AlphaDummy003
        x y A))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019
        A) ≠ (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)), ((nb081AlphaDummy004 A),
        (nb081AlphaDummy006 x y)), ((nb081AlphaDummy010 A), (nb081AlphaDummy011 x y)),
        ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)), ((nb081AlphaDummy004 A),
        (nb081AlphaDummy006 x y)), ((nb081AlphaDummy010 A), (nb081AlphaDummy011 x y)),
        ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy005 A) from
                                    (by
                                      unfold nb081AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb081_support_mem_0004 A)
                                              1)))) (show x ≠ (nb081AlphaDummy007 x y) from
                                    (by
                                      unfold nb081AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb081_support_mem_0006 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy004 A) from
                                      (by
                                        unfold nb081AlphaDummy004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0004 A)
                                                0)))) (show x ≠ (nb081AlphaDummy006 x y) from
                                      (by
                                        unfold nb081AlphaDummy006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb081_support_mem_0006 x y) 0))))
                                    (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy010 A) from (by
                                          unfold nb081AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0008 A) 0))))
                                      (show x ≠ (nb081AlphaDummy011 x y) from (by
                                          unfold nb081AlphaDummy011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0009 x y) 0))))
                                      (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy008 A) from (by
          unfold nb081AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0005 A) 0)))) (show x ≠ (nb081AlphaDummy009 x y) from
        (by
          unfold nb081AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb081AlphaDummy000 A))).fv ∪
                                      ((Class.cv (nb081AlphaDummy001 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb081AlphaDummy005 A) ≠
        (nb081AlphaDummy012 A) from (by
          unfold nb081AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy014 x y) from (by
          unfold nb081AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081AlphaDummy005 A) ≠ (nb081AlphaDummy013 A) from (by
          unfold nb081AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081AlphaDummy007 x y) ≠
        (nb081AlphaDummy015 x y) from (by
          unfold nb081AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081AlphaDummy005 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb081AlphaDummy007 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy019 A) from (by
          unfold
            nb081AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy022 x y) from (by
          unfold
            nb081AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy018 A) from (by
          unfold
            nb081AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy021 x y) from (by
          unfold
            nb081AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold
            nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold
            nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)), ((nb081AlphaDummy004 A),
        (nb081AlphaDummy006 x y)), ((nb081AlphaDummy010 A), (nb081AlphaDummy011 x y)),
        ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)), ((nb081AlphaDummy001 A),
        y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x
        y A))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy026 A) from (by
          unfold
            nb081AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy027 x y) from (by
          unfold
            nb081AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy024 A) from (by
          unfold
            nb081AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy025 x y) from (by
          unfold
            nb081AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy020 A), (nb081AlphaDummy023 x y)), ((nb081AlphaDummy019 A),
        (nb081AlphaDummy022 x y)), ((nb081AlphaDummy018 A), (nb081AlphaDummy021 x y)),
        ((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)), ((nb081AlphaDummy004 A),
        (nb081AlphaDummy006 x y)), ((nb081AlphaDummy010 A), (nb081AlphaDummy011 x y)),
        ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)), ((nb081AlphaDummy001 A),
        y), ((nb081AlphaDummy000 A), x), ((nb081AlphaDummy002 A), (nb081AlphaDummy003
        x y A))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081AlphaDummy012 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081AlphaDummy014 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy019
        A) ≠ (nb081AlphaDummy030 A) from (by
          unfold
            nb081AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy031 x y) from (by
          unfold
            nb081AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy019 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081AlphaDummy022 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081AlphaDummy012
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081AlphaDummy014 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy020
        A) ≠ (nb081AlphaDummy032 A) from (by
          unfold
            nb081AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy033 x y) from (by
          unfold
            nb081AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy020 A) ≠
        (nb081AlphaDummy028 A) from (by
          unfold
            nb081AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081AlphaDummy023 x y) ≠ (nb081AlphaDummy029 x y) from (by
          unfold
            nb081AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)), ((nb081AlphaDummy004 A),
        (nb081AlphaDummy006 x y)), ((nb081AlphaDummy010 A), (nb081AlphaDummy011 x y)),
        ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy012 A) ≠ (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081AlphaDummy012 A) ≠
        (nb081AlphaDummy016 A) from (by
          unfold nb081AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081AlphaDummy014 x y) ≠ (nb081AlphaDummy017 x y) from (by
          unfold nb081AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb081AlphaDummy016 A), (nb081AlphaDummy017 x y)), ((nb081AlphaDummy012 A),
        (nb081AlphaDummy014 x y)), ((nb081AlphaDummy013 A), (nb081AlphaDummy015 x y)),
        ((nb081AlphaDummy005 A), (nb081AlphaDummy007 x y)), ((nb081AlphaDummy004 A),
        (nb081AlphaDummy006 x y)), ((nb081AlphaDummy010 A), (nb081AlphaDummy011 x y)),
        ((nb081AlphaDummy008 A), (nb081AlphaDummy009 x y)),
        ((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
        ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb081SplitAlpha0000 x y A)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy046 A) from
                                      (by
                                        unfold nb081AlphaDummy046;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0048 A)
                                                0)))) (show x ≠ (nb081AlphaDummy047 x) from
                                      (by
                                        unfold nb081AlphaDummy047;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0049 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy044 A)
                                        from (by
                                          unfold nb081AlphaDummy044;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0046 A) 0))))
                                      (show x ≠ (nb081AlphaDummy045 x) from (by
                                          unfold nb081AlphaDummy045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0047 x) 0))))
                                      (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy042 A) from (by
          unfold nb081AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0044 A) 0)))) (show x ≠ (nb081AlphaDummy043 x) from (by
          unfold nb081AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0045 x) 0)))) (TAlphaVar.there (show
        (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy040 A) from (by
          unfold nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042 A) 0)))) (show x ≠ (nb081AlphaDummy041 x y) from
        (by
          unfold nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy046 A) from
                                      (by
                                        unfold nb081AlphaDummy046;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0048 A)
                                                0)))) (show x ≠ (nb081AlphaDummy047 x) from
                                      (by
                                        unfold nb081AlphaDummy047;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0049 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy044 A)
                                        from (by
                                          unfold nb081AlphaDummy044;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0046 A) 0))))
                                      (show x ≠ (nb081AlphaDummy045 x) from (by
                                          unfold nb081AlphaDummy045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0047 x) 0))))
                                      (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy042 A) from (by
          unfold nb081AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0044 A) 0)))) (show x ≠ (nb081AlphaDummy043 x) from (by
          unfold nb081AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0045 x) 0)))) (TAlphaVar.there (show
        (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy040 A) from (by
          unfold nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042 A) 0)))) (show x ≠ (nb081AlphaDummy041 x y) from
        (by
          unfold nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy046 A) from (by
          unfold nb081AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0048 A)
                  0)))) (show x ≠ (nb081AlphaDummy047 x) from (by
          unfold nb081AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0049 x)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy054 A) from (by
          unfold nb081AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0056
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy055 x) from (by
          unfold nb081AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy052 A) from (by
          unfold nb081AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0054
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy053 x y) from (by
          unfold nb081AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0055
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy050 A) from (by
          unfold
            nb081AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0052
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy051 x y) from (by
          unfold
            nb081AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy048 A) from (by
          unfold
            nb081AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0050
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy049 x y) from (by
          unfold
            nb081AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy040 A) from (by
          unfold
            nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy041 x y) from (by
          unfold
            nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy046 A) from (by
          unfold nb081AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0048 A)
                  0)))) (show x ≠ (nb081AlphaDummy047 x) from (by
          unfold nb081AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0049 x)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy054 A) from (by
          unfold nb081AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0056
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy055 x) from (by
          unfold nb081AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy052 A) from (by
          unfold nb081AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0054
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy053 x y) from (by
          unfold nb081AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0055
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy050 A) from (by
          unfold
            nb081AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0052
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy051 x y) from (by
          unfold
            nb081AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy048 A) from (by
          unfold
            nb081AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0050
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy049 x y) from (by
          unfold
            nb081AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy040 A) from (by
          unfold
            nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy041 x y) from (by
          unfold
            nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy058 A) from (by
          unfold nb081AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0068 A)
                  0)))) (show y ≠ (nb081AlphaDummy059 y) from (by
          unfold nb081AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0069 y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy056 A) from (by
          unfold nb081AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0066
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy057 y) from (by
          unfold nb081AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0067
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy052 A) from (by
          unfold nb081AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0064
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy053 x y) from (by
          unfold nb081AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy050 A) from (by
          unfold
            nb081AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0062
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy051 x y) from (by
          unfold
            nb081AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy048 A) from (by
          unfold
            nb081AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0060
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy049 x y) from (by
          unfold
            nb081AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0061
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy040 A) from (by
          unfold
            nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0058
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy041 x y) from (by
          unfold
            nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0059
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy058 A) from (by
          unfold nb081AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0068 A)
                  0)))) (show y ≠ (nb081AlphaDummy059 y) from (by
          unfold nb081AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0069 y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy056 A) from (by
          unfold nb081AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0066
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy057 y) from (by
          unfold nb081AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0067
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy052 A) from (by
          unfold nb081AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0064
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy053 x y) from (by
          unfold nb081AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy050 A) from (by
          unfold
            nb081AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0062
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy051 x y) from (by
          unfold
            nb081AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy048 A) from (by
          unfold
            nb081AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0060
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy049 x y) from (by
          unfold
            nb081AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0061
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy040 A) from (by
          unfold
            nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0058
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy041 x y) from (by
          unfold
            nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0059
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy046 A) from (by
          unfold nb081AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0048 A)
                  0)))) (show x ≠ (nb081AlphaDummy047 x) from (by
          unfold nb081AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0049 x)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy054 A) from (by
          unfold nb081AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0056
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy055 x) from (by
          unfold nb081AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy052 A) from (by
          unfold nb081AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0054
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy053 x y) from (by
          unfold nb081AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0055
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy050 A) from (by
          unfold
            nb081AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0052
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy051 x y) from (by
          unfold
            nb081AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy048 A) from (by
          unfold
            nb081AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0050
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy049 x y) from (by
          unfold
            nb081AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy040 A) from (by
          unfold
            nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy041 x y) from (by
          unfold
            nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy000 A) ≠ (nb081AlphaDummy046 A) from (by
          unfold nb081AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0048 A)
                  0)))) (show x ≠ (nb081AlphaDummy047 x) from (by
          unfold nb081AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0049 x)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy054 A) from (by
          unfold nb081AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0056
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy055 x) from (by
          unfold nb081AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy052 A) from (by
          unfold nb081AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0054
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy053 x y) from (by
          unfold nb081AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0055
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy050 A) from (by
          unfold
            nb081AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0052
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy051 x y) from (by
          unfold
            nb081AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy048 A) from (by
          unfold
            nb081AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0050
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy049 x y) from (by
          unfold
            nb081AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy000 A) ≠
        (nb081AlphaDummy040 A) from (by
          unfold
            nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042
                    A)
                  0)))) (show x ≠ (nb081AlphaDummy041 x y) from (by
          unfold
            nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy058 A) from (by
          unfold nb081AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0068 A)
                  0)))) (show y ≠ (nb081AlphaDummy059 y) from (by
          unfold nb081AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0069 y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy056 A) from (by
          unfold nb081AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0066
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy057 y) from (by
          unfold nb081AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0067
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy052 A) from (by
          unfold nb081AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0064
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy053 x y) from (by
          unfold nb081AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy050 A) from (by
          unfold
            nb081AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0062
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy051 x y) from (by
          unfold
            nb081AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy048 A) from (by
          unfold
            nb081AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0060
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy049 x y) from (by
          unfold
            nb081AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0061
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy040 A) from (by
          unfold
            nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0058
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy041 x y) from (by
          unfold
            nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0059
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081AlphaDummy001 A) ≠ (nb081AlphaDummy058 A) from (by
          unfold nb081AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0068 A)
                  0)))) (show y ≠ (nb081AlphaDummy059 y) from (by
          unfold nb081AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0069 y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy056 A) from (by
          unfold nb081AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0066
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy057 y) from (by
          unfold nb081AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0067
                    y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy052 A) from (by
          unfold nb081AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0064
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy053 x y) from (by
          unfold nb081AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy050 A) from (by
          unfold
            nb081AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0062
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy051 x y) from (by
          unfold
            nb081AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy048 A) from (by
          unfold
            nb081AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0060
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy049 x y) from (by
          unfold
            nb081AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0061
                    x y)
                  0)))) (TAlphaVar.there (show (nb081AlphaDummy001 A) ≠
        (nb081AlphaDummy040 A) from (by
          unfold
            nb081AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0058
                    A)
                  0)))) (show y ≠ (nb081AlphaDummy041 x y) from (by
          unfold
            nb081AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0059
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))))))))
        (TAlphaClass.reflOfReflOn
          [((nb081AlphaDummy001 A), y), ((nb081AlphaDummy000 A), x),
            ((nb081AlphaDummy002 A), (nb081AlphaDummy003 x y A))]
          A (nb081FocusedRefl0000 x y A dv_A_x dv_A_y)))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_kqrel`. -/
@[expose]
noncomputable def nominalDfKqrel (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCkqrel A) (synCopab x y (.classMem (synCopk (.cv x) (.cv y)) A))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.neg (nb081SplitAlpha0001 x y A dv_A_x dv_A_y dv_x_y)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
