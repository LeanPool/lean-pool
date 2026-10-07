/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C092M3Part002

/-! NF weak partition development: NAR4H5C092M3Part003. -/


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

/-- Checked nominal proof certificate identified upstream as `nb092_split_alpha_0003`. -/
@[expose]
noncomputable def nb092SplitAlpha0003 (x : Var) (y : Var) (R : Class) (a : Var)
    (b : Var) (dv_R_a : a ∉ R.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_a_b : a ≠ b) (dv_a_x : a ≠ x) (dv_b_x : b ≠ x)
    (dv_b_y : b ≠ y) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))]
      (Wff.imp (Wff.classEq (Class.cv (nb092AlphaDummy004 R))
          (synCop (Class.cv (nb092AlphaDummy000 R)) (Class.cv (nb092AlphaDummy001 R))))
        (Wff.neg (synWrex (nb092AlphaDummy002 R) (Class.cv (nb092AlphaDummy000 R))
            (synWrex (nb092AlphaDummy003 R) (Class.cv (nb092AlphaDummy001 R))
              (synWbr (Class.cv (nb092AlphaDummy002 R)) R
                (Class.cv (nb092AlphaDummy003 R)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb092AlphaDummy005 x y R a b))
          (synCop (Class.cv a) (Class.cv b))) (Wff.neg (synWrex x (Class.cv a)
            (synWrex y (Class.cv b) (synWbr (Class.cv x) R (Class.cv y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb092AlphaDummy001 R) ≠ (nb092AlphaDummy004 R) from (by
                unfold nb092AlphaDummy004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0002 R) 0)))))
          (Ne.symm (show b ≠ (nb092AlphaDummy005 x y R a b) from (by
                unfold nb092AlphaDummy005;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb092_support_mem_0003 x y R a b) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy004 R) from (by
                  unfold nb092AlphaDummy004;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0000 R) 0)))))
            (Ne.symm (show a ≠ (nb092AlphaDummy005 x y R a b) from (by
                  unfold nb092AlphaDummy005;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb092_support_mem_0001 x y R a b) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy007 R) from
                                    (by
                                      unfold nb092AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0004 R)
                                              1)))) (show a ≠ (nb092AlphaDummy009 a b) from
                                    (by
                                      unfold nb092AlphaDummy009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0006 a b)
                                              1)))) (TAlphaVar.there (show
                                      (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy006 R) from
                                      (by
                                        unfold nb092AlphaDummy006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb092_support_mem_0004 R)
                                                0)))) (show a ≠ (nb092AlphaDummy008 a b) from
                                      (by
                                        unfold nb092AlphaDummy008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb092_support_mem_0006 a b) 0))))
                                    (TAlphaVar.there (show (nb092AlphaDummy000 R) ≠
        (nb092AlphaDummy012 R) from (by
                                          unfold nb092AlphaDummy012;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0008 R) 0))))
                                      (show a ≠ (nb092AlphaDummy013 a b) from (by
                                          unfold nb092AlphaDummy013;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0009 a b) 0))))
                                      (TAlphaVar.there (show (nb092AlphaDummy000 R) ≠
        (nb092AlphaDummy010 R) from (by
          unfold nb092AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0005 R) 0)))) (show a ≠ (nb092AlphaDummy011 a b) from
        (by
          unfold nb092AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0007 a b) 0)))) (TAlphaVar.there
        (freshVar_injective ((R).fv) (by decide)) dv_a_b (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb092AlphaDummy000 R))).fv ∪
                                      ((Class.cv (nb092AlphaDummy001 R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb092AlphaDummy007 R) ≠
        (nb092AlphaDummy014 R) from (by
          unfold nb092AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 0)))) (show (nb092AlphaDummy009 a b) ≠
        (nb092AlphaDummy016 a b) from (by
          unfold nb092AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 0)))) (TAlphaVar.there (show
        (nb092AlphaDummy007 R) ≠ (nb092AlphaDummy015 R) from (by
          unfold nb092AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 1)))) (show (nb092AlphaDummy009 a b) ≠
        (nb092AlphaDummy017 a b) from (by
          unfold nb092AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092AlphaDummy007 R))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb092AlphaDummy009 a b))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy014 R) ≠ (nb092AlphaDummy021 R) from (by
          unfold
            nb092AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  1)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy024 a b) from (by
          unfold
            nb092AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  1)))) (TAlphaVar.there (show (nb092AlphaDummy014 R) ≠
        (nb092AlphaDummy020 R) from (by
          unfold
            nb092AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy023 a b) from (by
          unfold
            nb092AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy014 R) ≠
        (nb092AlphaDummy018 R) from (by
          unfold
            nb092AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy019 a b) from (by
          unfold
            nb092AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy022 R), (nb092AlphaDummy025 a b)), ((nb092AlphaDummy021 R),
        (nb092AlphaDummy024 a b)), ((nb092AlphaDummy020 R), (nb092AlphaDummy023 a b)),
        ((nb092AlphaDummy018 R), (nb092AlphaDummy019 a b)), ((nb092AlphaDummy014 R),
        (nb092AlphaDummy016 a b)), ((nb092AlphaDummy015 R), (nb092AlphaDummy017 a b)),
        ((nb092AlphaDummy007 R), (nb092AlphaDummy009 a b)), ((nb092AlphaDummy006 R),
        (nb092AlphaDummy008 a b)), ((nb092AlphaDummy012 R), (nb092AlphaDummy013 a b)),
        ((nb092AlphaDummy010 R), (nb092AlphaDummy011 a b)), ((nb092AlphaDummy001 R),
        b), ((nb092AlphaDummy000 R), a), ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x
        y R a b))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy021 R) ≠ (nb092AlphaDummy028 R) from (by
          unfold
            nb092AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy029 a b) from (by
          unfold
            nb092AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy026 R) from (by
          unfold
            nb092AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy027 a b) from (by
          unfold
            nb092AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy014
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy022
        R) ≠ (nb092AlphaDummy028 R) from (by
          unfold
            nb092AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy029 a b) from (by
          unfold
            nb092AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠
        (nb092AlphaDummy026 R) from (by
          unfold
            nb092AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy027 a b) from (by
          unfold
            nb092AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠ (nb092AlphaDummy028 R) from (by
          unfold
            nb092AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy029 a b) from (by
          unfold
            nb092AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy026 R) from (by
          unfold
            nb092AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy027 a b) from (by
          unfold
            nb092AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy014
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy022
        R) ≠ (nb092AlphaDummy028 R) from (by
          unfold
            nb092AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy029 a b) from (by
          unfold
            nb092AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠
        (nb092AlphaDummy026 R) from (by
          unfold
            nb092AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy027 a b) from (by
          unfold
            nb092AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy022 R), (nb092AlphaDummy025 a b)), ((nb092AlphaDummy021 R),
        (nb092AlphaDummy024 a b)), ((nb092AlphaDummy020 R), (nb092AlphaDummy023 a b)),
        ((nb092AlphaDummy018 R), (nb092AlphaDummy019 a b)), ((nb092AlphaDummy014 R),
        (nb092AlphaDummy016 a b)), ((nb092AlphaDummy015 R), (nb092AlphaDummy017 a b)),
        ((nb092AlphaDummy007 R), (nb092AlphaDummy009 a b)), ((nb092AlphaDummy006 R),
        (nb092AlphaDummy008 a b)), ((nb092AlphaDummy012 R), (nb092AlphaDummy013 a b)),
        ((nb092AlphaDummy010 R), (nb092AlphaDummy011 a b)), ((nb092AlphaDummy001 R),
        b), ((nb092AlphaDummy000 R), a), ((nb092AlphaDummy004 R), (nb092AlphaDummy005
        x y R a b))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy032 R) from (by
          unfold
            nb092AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy033 a b) from (by
          unfold
            nb092AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy030 R) from (by
          unfold
            nb092AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy031 a b) from (by
          unfold
            nb092AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy014
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy021
        R) ≠ (nb092AlphaDummy032 R) from (by
          unfold
            nb092AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy033 a b) from (by
          unfold
            nb092AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy030 R) from (by
          unfold
            nb092AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy031 a b) from (by
          unfold
            nb092AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy014
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠ (nb092AlphaDummy034 R) from (by
          unfold
            nb092AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy035 a b) from (by
          unfold
            nb092AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠
        (nb092AlphaDummy030 R) from (by
          unfold
            nb092AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy031 a b) from (by
          unfold
            nb092AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy022
        R) ≠ (nb092AlphaDummy034 R) from (by
          unfold
            nb092AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy035 a b) from (by
          unfold
            nb092AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠
        (nb092AlphaDummy030 R) from (by
          unfold
            nb092AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy031 a b) from (by
          unfold
            nb092AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy014 R) ≠
        (nb092AlphaDummy018 R) from (by
          unfold nb092AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy019 a b) from (by
          unfold nb092AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy018 R), (nb092AlphaDummy019 a b)), ((nb092AlphaDummy014 R),
        (nb092AlphaDummy016 a b)), ((nb092AlphaDummy015 R), (nb092AlphaDummy017 a b)),
        ((nb092AlphaDummy007 R), (nb092AlphaDummy009 a b)), ((nb092AlphaDummy006 R),
        (nb092AlphaDummy008 a b)), ((nb092AlphaDummy012 R), (nb092AlphaDummy013 a b)),
        ((nb092AlphaDummy010 R), (nb092AlphaDummy011 a b)),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy014 R) ≠ (nb092AlphaDummy018 R) from (by
          unfold nb092AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy019 a b) from (by
          unfold nb092AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy014 R) ≠
        (nb092AlphaDummy018 R) from (by
          unfold nb092AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy019 a b) from (by
          unfold nb092AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy018 R), (nb092AlphaDummy019 a b)), ((nb092AlphaDummy014 R),
        (nb092AlphaDummy016 a b)), ((nb092AlphaDummy015 R), (nb092AlphaDummy017 a b)),
        ((nb092AlphaDummy007 R), (nb092AlphaDummy009 a b)), ((nb092AlphaDummy006 R),
        (nb092AlphaDummy008 a b)), ((nb092AlphaDummy012 R), (nb092AlphaDummy013 a b)),
        ((nb092AlphaDummy010 R), (nb092AlphaDummy011 a b)),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy007 R) from
                                    (by
                                      unfold nb092AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0004 R)
                                              1)))) (show a ≠ (nb092AlphaDummy009 a b) from
                                    (by
                                      unfold nb092AlphaDummy009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0006 a b)
                                              1)))) (TAlphaVar.there (show
                                      (nb092AlphaDummy000 R) ≠ (nb092AlphaDummy006 R) from
                                      (by
                                        unfold nb092AlphaDummy006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb092_support_mem_0004 R)
                                                0)))) (show a ≠ (nb092AlphaDummy008 a b) from
                                      (by
                                        unfold nb092AlphaDummy008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb092_support_mem_0006 a b) 0))))
                                    (TAlphaVar.there (show (nb092AlphaDummy000 R) ≠
        (nb092AlphaDummy012 R) from (by
                                          unfold nb092AlphaDummy012;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0008 R) 0))))
                                      (show a ≠ (nb092AlphaDummy013 a b) from (by
                                          unfold nb092AlphaDummy013;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0009 a b) 0))))
                                      (TAlphaVar.there (show (nb092AlphaDummy000 R) ≠
        (nb092AlphaDummy010 R) from (by
          unfold nb092AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0005 R) 0)))) (show a ≠ (nb092AlphaDummy011 a b) from
        (by
          unfold nb092AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0007 a b) 0)))) (TAlphaVar.there
        (freshVar_injective ((R).fv) (by decide)) dv_a_b (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb092AlphaDummy000 R))).fv ∪
                                      ((Class.cv (nb092AlphaDummy001 R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb092AlphaDummy007 R) ≠
        (nb092AlphaDummy014 R) from (by
          unfold nb092AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 0)))) (show (nb092AlphaDummy009 a b) ≠
        (nb092AlphaDummy016 a b) from (by
          unfold nb092AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 0)))) (TAlphaVar.there (show
        (nb092AlphaDummy007 R) ≠ (nb092AlphaDummy015 R) from (by
          unfold nb092AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 1)))) (show (nb092AlphaDummy009 a b) ≠
        (nb092AlphaDummy017 a b) from (by
          unfold nb092AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092AlphaDummy007 R))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb092AlphaDummy009 a b))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy014 R) ≠ (nb092AlphaDummy021 R) from (by
          unfold
            nb092AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  1)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy024 a b) from (by
          unfold
            nb092AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  1)))) (TAlphaVar.there (show (nb092AlphaDummy014 R) ≠
        (nb092AlphaDummy020 R) from (by
          unfold
            nb092AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy023 a b) from (by
          unfold
            nb092AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy014 R) ≠
        (nb092AlphaDummy018 R) from (by
          unfold
            nb092AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy019 a b) from (by
          unfold
            nb092AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy022 R), (nb092AlphaDummy025 a b)), ((nb092AlphaDummy021 R),
        (nb092AlphaDummy024 a b)), ((nb092AlphaDummy020 R), (nb092AlphaDummy023 a b)),
        ((nb092AlphaDummy018 R), (nb092AlphaDummy019 a b)), ((nb092AlphaDummy014 R),
        (nb092AlphaDummy016 a b)), ((nb092AlphaDummy015 R), (nb092AlphaDummy017 a b)),
        ((nb092AlphaDummy007 R), (nb092AlphaDummy009 a b)), ((nb092AlphaDummy006 R),
        (nb092AlphaDummy008 a b)), ((nb092AlphaDummy012 R), (nb092AlphaDummy013 a b)),
        ((nb092AlphaDummy010 R), (nb092AlphaDummy011 a b)), ((nb092AlphaDummy001 R),
        b), ((nb092AlphaDummy000 R), a), ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x
        y R a b))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy021 R) ≠ (nb092AlphaDummy028 R) from (by
          unfold
            nb092AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy029 a b) from (by
          unfold
            nb092AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy026 R) from (by
          unfold
            nb092AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy027 a b) from (by
          unfold
            nb092AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy014
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy022
        R) ≠ (nb092AlphaDummy028 R) from (by
          unfold
            nb092AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy029 a b) from (by
          unfold
            nb092AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠
        (nb092AlphaDummy026 R) from (by
          unfold
            nb092AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy027 a b) from (by
          unfold
            nb092AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠ (nb092AlphaDummy028 R) from (by
          unfold
            nb092AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy029 a b) from (by
          unfold
            nb092AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy026 R) from (by
          unfold
            nb092AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy027 a b) from (by
          unfold
            nb092AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy014
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy022
        R) ≠ (nb092AlphaDummy028 R) from (by
          unfold
            nb092AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy029 a b) from (by
          unfold
            nb092AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠
        (nb092AlphaDummy026 R) from (by
          unfold
            nb092AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy027 a b) from (by
          unfold
            nb092AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy022 R), (nb092AlphaDummy025 a b)), ((nb092AlphaDummy021 R),
        (nb092AlphaDummy024 a b)), ((nb092AlphaDummy020 R), (nb092AlphaDummy023 a b)),
        ((nb092AlphaDummy018 R), (nb092AlphaDummy019 a b)), ((nb092AlphaDummy014 R),
        (nb092AlphaDummy016 a b)), ((nb092AlphaDummy015 R), (nb092AlphaDummy017 a b)),
        ((nb092AlphaDummy007 R), (nb092AlphaDummy009 a b)), ((nb092AlphaDummy006 R),
        (nb092AlphaDummy008 a b)), ((nb092AlphaDummy012 R), (nb092AlphaDummy013 a b)),
        ((nb092AlphaDummy010 R), (nb092AlphaDummy011 a b)), ((nb092AlphaDummy001 R),
        b), ((nb092AlphaDummy000 R), a), ((nb092AlphaDummy004 R), (nb092AlphaDummy005
        x y R a b))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092AlphaDummy014 R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092AlphaDummy016 a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy032 R) from (by
          unfold
            nb092AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy033 a b) from (by
          unfold
            nb092AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy030 R) from (by
          unfold
            nb092AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy031 a b) from (by
          unfold
            nb092AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy014
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy021
        R) ≠ (nb092AlphaDummy032 R) from (by
          unfold
            nb092AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy033 a b) from (by
          unfold
            nb092AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy021 R) ≠
        (nb092AlphaDummy030 R) from (by
          unfold
            nb092AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092AlphaDummy024 a b) ≠ (nb092AlphaDummy031 a b) from (by
          unfold
            nb092AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy014
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy016 a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠ (nb092AlphaDummy034 R) from (by
          unfold
            nb092AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy035 a b) from (by
          unfold
            nb092AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠
        (nb092AlphaDummy030 R) from (by
          unfold
            nb092AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy031 a b) from (by
          unfold
            nb092AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy022
        R) ≠ (nb092AlphaDummy034 R) from (by
          unfold
            nb092AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy035 a b) from (by
          unfold
            nb092AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy022 R) ≠
        (nb092AlphaDummy030 R) from (by
          unfold
            nb092AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092AlphaDummy025 a b) ≠ (nb092AlphaDummy031 a b) from (by
          unfold
            nb092AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy014 R) ≠
        (nb092AlphaDummy018 R) from (by
          unfold nb092AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy019 a b) from (by
          unfold nb092AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy018 R), (nb092AlphaDummy019 a b)), ((nb092AlphaDummy014 R),
        (nb092AlphaDummy016 a b)), ((nb092AlphaDummy015 R), (nb092AlphaDummy017 a b)),
        ((nb092AlphaDummy007 R), (nb092AlphaDummy009 a b)), ((nb092AlphaDummy006 R),
        (nb092AlphaDummy008 a b)), ((nb092AlphaDummy012 R), (nb092AlphaDummy013 a b)),
        ((nb092AlphaDummy010 R), (nb092AlphaDummy011 a b)),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy014 R) ≠ (nb092AlphaDummy018 R) from (by
          unfold nb092AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy019 a b) from (by
          unfold nb092AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy014 R) ≠
        (nb092AlphaDummy018 R) from (by
          unfold nb092AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092AlphaDummy016 a b) ≠ (nb092AlphaDummy019 a b) from (by
          unfold nb092AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy018 R), (nb092AlphaDummy019 a b)), ((nb092AlphaDummy014 R),
        (nb092AlphaDummy016 a b)), ((nb092AlphaDummy015 R), (nb092AlphaDummy017 a b)),
        ((nb092AlphaDummy007 R), (nb092AlphaDummy009 a b)), ((nb092AlphaDummy006 R),
        (nb092AlphaDummy008 a b)), ((nb092AlphaDummy012 R), (nb092AlphaDummy013 a b)),
        ((nb092AlphaDummy010 R), (nb092AlphaDummy011 a b)),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb092SplitAlpha0000 x y R a b)))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (freshVar_injective ((R).fv) (by decide)) dv_a_x
                (TAlphaVar.there (freshVar_injective ((R).fv) (by decide)) dv_a_b
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective ((R).fv) (by decide)) dv_b_y
                    (TAlphaVar.there (freshVar_injective ((R).fv) (by decide)) dv_b_x
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb092SplitAlpha0002 x y R a b dv_x_y))))
                (TAlphaClass.reflOfReflOn
                  [((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
                    ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
                    ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] R
                  (nb092FocusedRefl0000 x y R a b dv_R_a dv_R_b dv_R_x dv_R_y)))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_lnqrel`. -/
@[expose]
noncomputable def nominalDfLnqrel (x : Var) (y : Var) (R : Class) (a : Var) (b : Var)
    (dv_R_a : a ∉ R.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_a_b : a ≠ b) (dv_a_x : a ≠ x) (__dv_a_y : a ≠ y) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synClnqrel R) (synCopab a b
          (synWrex x (.cv a) (synWrex y (.cv b) (synWbr (.cv x) R (.cv y)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
              (nb092SplitAlpha0003 x y R a b dv_R_a dv_R_b dv_R_x dv_R_y dv_a_b dv_a_x
                dv_b_x dv_b_y dv_x_y)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
