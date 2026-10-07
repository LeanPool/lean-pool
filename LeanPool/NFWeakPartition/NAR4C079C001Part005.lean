/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C079C001Part004

/-! NF weak partition development: NAR4C079C001Part005. -/


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

/-- Checked nominal proof certificate identified upstream as `nb079_split_alpha_0001`. -/
@[expose]
noncomputable def nb079SplitAlpha0001 (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)]
      (Wff.imp (Wff.classEq (Class.cv (nb079AlphaDummy002 A))
          (synCopk (Class.cv (nb079AlphaDummy000 A)) (Class.cv (nb079AlphaDummy001 A))))
        (Wff.neg (Wff.classMem (synCop (Class.cv (nb079AlphaDummy000 A))
              (Class.cv (nb079AlphaDummy001 A))) A)))
      (Wff.imp (Wff.classEq (Class.cv z) (synCopk (Class.cv x) (Class.cv y)))
        (Wff.neg (Wff.classMem (synCop (Class.cv x) (Class.cv y)) A))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_y_z)
          (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_x_z)
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy009 A) from
                                    (by
                                      unfold nb079AlphaDummy009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb079_support_mem_0006 A)
                                              0)))) (show x ≠ (nb079AlphaDummy010 x) from (by
                                      unfold nb079AlphaDummy010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb079_support_mem_0007 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy007 A) from
                                      (by
                                        unfold nb079AlphaDummy007;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0004 A)
                                                0)))) (show x ≠ (nb079AlphaDummy008 x) from
                                      (by
                                        unfold nb079AlphaDummy008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0005 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy005 A)
                                        from (by
                                          unfold nb079AlphaDummy005;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0002 A) 0))))
                                      (show x ≠ (nb079AlphaDummy006 x) from (by
                                          unfold nb079AlphaDummy006;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0003 x) 0))))
                                      (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000 A) 0)))) (show x ≠ (nb079AlphaDummy004 x y) from
        (by
          unfold nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy009 A) from
                                    (by
                                      unfold nb079AlphaDummy009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb079_support_mem_0006 A)
                                              0)))) (show x ≠ (nb079AlphaDummy010 x) from (by
                                      unfold nb079AlphaDummy010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb079_support_mem_0007 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy007 A) from
                                      (by
                                        unfold nb079AlphaDummy007;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0004 A)
                                                0)))) (show x ≠ (nb079AlphaDummy008 x) from
                                      (by
                                        unfold nb079AlphaDummy008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0005 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy005 A)
                                        from (by
                                          unfold nb079AlphaDummy005;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0002 A) 0))))
                                      (show x ≠ (nb079AlphaDummy006 x) from (by
                                          unfold nb079AlphaDummy006;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0003 x) 0))))
                                      (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000 A) 0)))) (show x ≠ (nb079AlphaDummy004 x y) from
        (by
          unfold nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy009 A) from (by
          unfold nb079AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0006 A)
                  0)))) (show x ≠ (nb079AlphaDummy010 x) from (by
          unfold nb079AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0007 x)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy017 A) from (by
          unfold nb079AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0014 A)
                  0)))) (show x ≠ (nb079AlphaDummy018 x) from (by
          unfold nb079AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0015 x)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy015 A) from (by
          unfold nb079AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0012
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy016 x y) from (by
          unfold nb079AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy013 A) from (by
          unfold nb079AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0010
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy014 x y) from (by
          unfold nb079AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy011 A) from (by
          unfold
            nb079AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0008
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy012 x y) from (by
          unfold
            nb079AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold
            nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy004 x y) from (by
          unfold
            nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy009 A) from (by
          unfold nb079AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0006 A)
                  0)))) (show x ≠ (nb079AlphaDummy010 x) from (by
          unfold nb079AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0007 x)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy017 A) from (by
          unfold nb079AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0014 A)
                  0)))) (show x ≠ (nb079AlphaDummy018 x) from (by
          unfold nb079AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0015 x)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy015 A) from (by
          unfold nb079AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0012
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy016 x y) from (by
          unfold nb079AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy013 A) from (by
          unfold nb079AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0010
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy014 x y) from (by
          unfold nb079AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy011 A) from (by
          unfold
            nb079AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0008
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy012 x y) from (by
          unfold
            nb079AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold
            nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy004 x y) from (by
          unfold
            nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy021 A) from (by
          unfold nb079AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0026 A)
                  0)))) (show y ≠ (nb079AlphaDummy022 y) from (by
          unfold nb079AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0027 y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy019 A) from (by
          unfold nb079AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0024 A)
                  0)))) (show y ≠ (nb079AlphaDummy020 y) from (by
          unfold nb079AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0025 y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy015 A) from (by
          unfold nb079AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0022
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy016 x y) from (by
          unfold nb079AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0023
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy013 A) from (by
          unfold nb079AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0020
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy014 x y) from (by
          unfold nb079AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0021
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy011 A) from (by
          unfold
            nb079AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0018
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy012 x y) from (by
          unfold
            nb079AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0019
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold
            nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0016
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy004 x y) from (by
          unfold
            nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0017
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy021 A) from (by
          unfold nb079AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0026 A)
                  0)))) (show y ≠ (nb079AlphaDummy022 y) from (by
          unfold nb079AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0027 y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy019 A) from (by
          unfold nb079AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0024 A)
                  0)))) (show y ≠ (nb079AlphaDummy020 y) from (by
          unfold nb079AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0025 y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy015 A) from (by
          unfold nb079AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0022
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy016 x y) from (by
          unfold nb079AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0023
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy013 A) from (by
          unfold nb079AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0020
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy014 x y) from (by
          unfold nb079AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0021
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy011 A) from (by
          unfold
            nb079AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0018
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy012 x y) from (by
          unfold
            nb079AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0019
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold
            nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0016
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy004 x y) from (by
          unfold
            nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0017
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy009 A) from (by
          unfold nb079AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0006 A)
                  0)))) (show x ≠ (nb079AlphaDummy010 x) from (by
          unfold nb079AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0007 x)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy017 A) from (by
          unfold nb079AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0014 A)
                  0)))) (show x ≠ (nb079AlphaDummy018 x) from (by
          unfold nb079AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0015 x)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy015 A) from (by
          unfold nb079AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0012
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy016 x y) from (by
          unfold nb079AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy013 A) from (by
          unfold nb079AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0010
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy014 x y) from (by
          unfold nb079AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy011 A) from (by
          unfold
            nb079AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0008
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy012 x y) from (by
          unfold
            nb079AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold
            nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy004 x y) from (by
          unfold
            nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy009 A) from (by
          unfold nb079AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0006 A)
                  0)))) (show x ≠ (nb079AlphaDummy010 x) from (by
          unfold nb079AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0007 x)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy017 A) from (by
          unfold nb079AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0014 A)
                  0)))) (show x ≠ (nb079AlphaDummy018 x) from (by
          unfold nb079AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0015 x)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy015 A) from (by
          unfold nb079AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0012
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy016 x y) from (by
          unfold nb079AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy013 A) from (by
          unfold nb079AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0010
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy014 x y) from (by
          unfold nb079AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy011 A) from (by
          unfold
            nb079AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0008
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy012 x y) from (by
          unfold
            nb079AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold
            nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000
                    A)
                  0)))) (show x ≠ (nb079AlphaDummy004 x y) from (by
          unfold
            nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy021 A) from (by
          unfold nb079AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0026 A)
                  0)))) (show y ≠ (nb079AlphaDummy022 y) from (by
          unfold nb079AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0027 y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy019 A) from (by
          unfold nb079AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0024 A)
                  0)))) (show y ≠ (nb079AlphaDummy020 y) from (by
          unfold nb079AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0025 y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy015 A) from (by
          unfold nb079AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0022
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy016 x y) from (by
          unfold nb079AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0023
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy013 A) from (by
          unfold nb079AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0020
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy014 x y) from (by
          unfold nb079AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0021
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy011 A) from (by
          unfold
            nb079AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0018
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy012 x y) from (by
          unfold
            nb079AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0019
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold
            nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0016
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy004 x y) from (by
          unfold
            nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0017
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy001 A) ≠ (nb079AlphaDummy021 A) from (by
          unfold nb079AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0026 A)
                  0)))) (show y ≠ (nb079AlphaDummy022 y) from (by
          unfold nb079AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0027 y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy019 A) from (by
          unfold nb079AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0024 A)
                  0)))) (show y ≠ (nb079AlphaDummy020 y) from (by
          unfold nb079AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0025 y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy015 A) from (by
          unfold nb079AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0022
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy016 x y) from (by
          unfold nb079AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0023
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy013 A) from (by
          unfold nb079AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0020
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy014 x y) from (by
          unfold nb079AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0021
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy011 A) from (by
          unfold
            nb079AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0018
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy012 x y) from (by
          unfold
            nb079AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0019
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy001 A) ≠
        (nb079AlphaDummy003 A) from (by
          unfold
            nb079AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0016
                    A)
                  0)))) (show y ≠ (nb079AlphaDummy004 x y) from (by
          unfold
            nb079AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0017
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy024 A) from
                                      (by
                                        unfold nb079AlphaDummy024;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0028 A)
                                                1)))) (show x ≠ (nb079AlphaDummy026 x y) from
                                      (by
                                        unfold nb079AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb079_support_mem_0030 x y) 1))))
                                    (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy023 A) from (by
                                          unfold nb079AlphaDummy023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0028 A) 0))))
                                      (show x ≠ (nb079AlphaDummy025 x y) from (by
                                          unfold nb079AlphaDummy025;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0030 x y) 0))))
                                      (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy029 A) from (by
          unfold nb079AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0032 A) 0)))) (show x ≠ (nb079AlphaDummy030 x y) from
        (by
          unfold nb079AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0033 x y) 0)))) (TAlphaVar.there (show
        (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy027 A) from (by
          unfold nb079AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0029 A) 0)))) (show x ≠ (nb079AlphaDummy028 x y) from
        (by
          unfold nb079AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0031 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb079AlphaDummy000 A))).fv ∪
                                        ((Class.cv (nb079AlphaDummy001 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy031 A) from (by
          unfold nb079AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 0)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy033 x y) from (by
          unfold nb079AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 0)))) (TAlphaVar.there (show
        (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy032 A) from (by
          unfold nb079AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 1)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy034 x y) from (by
          unfold nb079AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy024 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy026 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031
        A) ≠ (nb079AlphaDummy038 A) from (by
          unfold
            nb079AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  1)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy041 x y) from (by
          unfold
            nb079AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  1)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy037 A) from (by
          unfold
            nb079AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy040 x y) from (by
          unfold
            nb079AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold
            nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold
            nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)), ((nb079AlphaDummy023 A),
        (nb079AlphaDummy025 x y)), ((nb079AlphaDummy029 A), (nb079AlphaDummy030 x y)),
        ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)), ((nb079AlphaDummy001 A),
        y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002 A), z)] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)), ((nb079AlphaDummy023 A),
        (nb079AlphaDummy025 x y)), ((nb079AlphaDummy029 A), (nb079AlphaDummy030 x y)),
        ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)), ((nb079AlphaDummy001 A),
        y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002 A), z)] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038
        A) ≠ (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)), ((nb079AlphaDummy023 A),
        (nb079AlphaDummy025 x y)), ((nb079AlphaDummy029 A), (nb079AlphaDummy030 x y)),
        ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)), ((nb079AlphaDummy023 A),
        (nb079AlphaDummy025 x y)), ((nb079AlphaDummy029 A), (nb079AlphaDummy030 x y)),
        ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy024 A) from
                                      (by
                                        unfold nb079AlphaDummy024;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0028 A)
                                                1)))) (show x ≠ (nb079AlphaDummy026 x y) from
                                      (by
                                        unfold nb079AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb079_support_mem_0030 x y) 1))))
                                    (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy023 A) from (by
                                          unfold nb079AlphaDummy023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0028 A) 0))))
                                      (show x ≠ (nb079AlphaDummy025 x y) from (by
                                          unfold nb079AlphaDummy025;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0030 x y) 0))))
                                      (TAlphaVar.there (show (nb079AlphaDummy000 A) ≠
        (nb079AlphaDummy029 A) from (by
          unfold nb079AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0032 A) 0)))) (show x ≠ (nb079AlphaDummy030 x y) from
        (by
          unfold nb079AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0033 x y) 0)))) (TAlphaVar.there (show
        (nb079AlphaDummy000 A) ≠ (nb079AlphaDummy027 A) from (by
          unfold nb079AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0029 A) 0)))) (show x ≠ (nb079AlphaDummy028 x y) from
        (by
          unfold nb079AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0031 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb079AlphaDummy000 A))).fv ∪
                                        ((Class.cv (nb079AlphaDummy001 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy031 A) from (by
          unfold nb079AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 0)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy033 x y) from (by
          unfold nb079AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 0)))) (TAlphaVar.there (show
        (nb079AlphaDummy024 A) ≠ (nb079AlphaDummy032 A) from (by
          unfold nb079AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 1)))) (show (nb079AlphaDummy026 x y) ≠
        (nb079AlphaDummy034 x y) from (by
          unfold nb079AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy024 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy026 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031
        A) ≠ (nb079AlphaDummy038 A) from (by
          unfold
            nb079AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  1)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy041 x y) from (by
          unfold
            nb079AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  1)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy037 A) from (by
          unfold
            nb079AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy040 x y) from (by
          unfold
            nb079AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold
            nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold
            nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)), ((nb079AlphaDummy023 A),
        (nb079AlphaDummy025 x y)), ((nb079AlphaDummy029 A), (nb079AlphaDummy030 x y)),
        ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)), ((nb079AlphaDummy001 A),
        y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002 A), z)] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy045 A) from (by
          unfold
            nb079AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy046 x y) from (by
          unfold
            nb079AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy043 A) from (by
          unfold
            nb079AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy044 x y) from (by
          unfold
            nb079AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy039 A), (nb079AlphaDummy042 x y)), ((nb079AlphaDummy038 A),
        (nb079AlphaDummy041 x y)), ((nb079AlphaDummy037 A), (nb079AlphaDummy040 x y)),
        ((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)), ((nb079AlphaDummy023 A),
        (nb079AlphaDummy025 x y)), ((nb079AlphaDummy029 A), (nb079AlphaDummy030 x y)),
        ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)), ((nb079AlphaDummy001 A),
        y), ((nb079AlphaDummy000 A), x), ((nb079AlphaDummy002 A), z)] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb079AlphaDummy031 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079AlphaDummy033 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy038
        A) ≠ (nb079AlphaDummy049 A) from (by
          unfold
            nb079AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy050 x y) from (by
          unfold
            nb079AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy038 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079AlphaDummy041 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079AlphaDummy031
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079AlphaDummy033 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy039
        A) ≠ (nb079AlphaDummy051 A) from (by
          unfold
            nb079AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy052 x y) from (by
          unfold
            nb079AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079AlphaDummy039 A) ≠
        (nb079AlphaDummy047 A) from (by
          unfold
            nb079AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079AlphaDummy042 x y) ≠ (nb079AlphaDummy048 x y) from (by
          unfold
            nb079AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)), ((nb079AlphaDummy023 A),
        (nb079AlphaDummy025 x y)), ((nb079AlphaDummy029 A), (nb079AlphaDummy030 x y)),
        ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079AlphaDummy031 A) ≠
        (nb079AlphaDummy035 A) from (by
          unfold nb079AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079AlphaDummy033 x y) ≠ (nb079AlphaDummy036 x y) from (by
          unfold nb079AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb079AlphaDummy035 A), (nb079AlphaDummy036 x y)), ((nb079AlphaDummy031 A),
        (nb079AlphaDummy033 x y)), ((nb079AlphaDummy032 A), (nb079AlphaDummy034 x y)),
        ((nb079AlphaDummy024 A), (nb079AlphaDummy026 x y)), ((nb079AlphaDummy023 A),
        (nb079AlphaDummy025 x y)), ((nb079AlphaDummy029 A), (nb079AlphaDummy030 x y)),
        ((nb079AlphaDummy027 A), (nb079AlphaDummy028 x y)),
        ((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
        ((nb079AlphaDummy002 A), z)] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb079SplitAlpha0000 x y z A))))))))
        (TAlphaClass.reflOfReflOn
          [((nb079AlphaDummy001 A), y), ((nb079AlphaDummy000 A), x),
            ((nb079AlphaDummy002 A), z)]
          A (nb079FocusedRefl0000 x y z A dv_A_x dv_A_y dv_A_z)))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_qkrel`. -/
@[expose]
noncomputable def nominalDfQkrel (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCqkrel A) (.cab z (synWex x (synWex y
              (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
                (.classMem (synCop (.cv x) (.cv y)) A)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
              (nb079SplitAlpha0001 x y z A dv_A_x dv_A_y dv_A_z dv_x_y dv_x_z dv_y_z)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
