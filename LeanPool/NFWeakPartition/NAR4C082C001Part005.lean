/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C082C001Part004

/-! NF weak partition development: NAR4C082C001Part005. -/


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

/-- Checked nominal proof certificate identified upstream as `nb082_split_alpha_0002`. -/
@[expose]
noncomputable def nb082SplitAlpha0002 (A : Class) (B : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p),
        ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
      (Wff.classEq (Class.cv (nb082AlphaDummy003 A B R))
        (synCop (Class.cv (nb082AlphaDummy000 A B R))
          (Class.cv (nb082AlphaDummy001 A B R))))
      (Wff.classEq (Class.cv (nb082AlphaDummy004 A B R p))
        (synCop (Class.cv p) (Class.cv (nb082AlphaDummy002 A B R p)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy003 A B R) from (by
              unfold nb082AlphaDummy003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0002 A B R) 0)))))
        (Ne.symm (show (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy004 A B R p) from
            (by
              unfold nb082AlphaDummy004;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0003 A B R p) 0)))))
        (TAlphaVar.there (Ne.symm
            (show (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy003 A B R) from (by
                unfold nb082AlphaDummy003;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0000 A B R) 0)))))
          (Ne.symm (show p ≠ (nb082AlphaDummy004 A B R p) from (by
                unfold nb082AlphaDummy004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb082_support_mem_0001 A B R p) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy006 A B R)
                                  from (by
                                    unfold nb082AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0006 A B R)
                                            1)))) (show p ≠ (nb082AlphaDummy008 A B R p) from
                                  (by
                                    unfold nb082AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb082_support_mem_0008 A B R p) 1))))
                                (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
                                      (nb082AlphaDummy005 A B R) from (by
                                      unfold nb082AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0006 A B R) 0))))
                                  (show p ≠ (nb082AlphaDummy007 A B R p) from (by
                                      unfold nb082AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0008 A B R p) 0))))
                                  (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
                                        (nb082AlphaDummy011 A B R) from (by
                                        unfold nb082AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0010 A B R) 0))))
                                    (show p ≠ (nb082AlphaDummy012 A B R p) from (by
                                        unfold nb082AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0011 A B R p) 0))))
                                    (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy009 A B R) from (by
                                          unfold nb082AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0007 A B R) 0))))
                                      (show p ≠ (nb082AlphaDummy010 A B R p) from (by
                                          unfold nb082AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0009 A B R p) 0))))
                                      (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy001 A B R) from (by
          unfold nb082AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0004 A B R) 0))))
                                        (show p ≠ (nb082AlphaDummy002 A B R p) from (by
          unfold nb082AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0005 A B R p) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
                                    ((Class.cv (nb082AlphaDummy001 A B R))).fv) (by decide))
                                (freshVar_injective (((Class.cv p)).fv ∪
                                    ((Class.cv (nb082AlphaDummy002 A B R p))).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy013 A B R) from (by
          unfold nb082AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 0)))) (show (nb082AlphaDummy008 A B R p) ≠
        (nb082AlphaDummy015 A B R p) from (by
          unfold nb082AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p) 0)))) (TAlphaVar.there (show
        (nb082AlphaDummy006 A B R) ≠ (nb082AlphaDummy014 A B R) from (by
          unfold nb082AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 1)))) (show (nb082AlphaDummy008 A B R p) ≠
        (nb082AlphaDummy016 A B R p) from (by
          unfold nb082AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb082AlphaDummy006 A B R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082AlphaDummy008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082AlphaDummy013 A B R) ≠ (nb082AlphaDummy020 A B R) from (by
          unfold
            nb082AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  1)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy023 A B R p)
        from (by
          unfold
            nb082AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  1)))) (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy019 A B R) from (by
          unfold
            nb082AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy022 A B R p)
        from (by
          unfold
            nb082AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold
            nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014
                    A B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold
            nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy021 A B R), (nb082AlphaDummy024 A B R p)),
        ((nb082AlphaDummy020 A B R), (nb082AlphaDummy023 A B R p)),
        ((nb082AlphaDummy019 A B R), (nb082AlphaDummy022 A B R p)),
        ((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy011 A B R), (nb082AlphaDummy012 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy027 A B R) from (by
          unfold
            nb082AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy028 A B R p)
        from (by
          unfold
            nb082AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy025 A B R) from (by
          unfold
            nb082AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy026 A B R p)
        from (by
          unfold
            nb082AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021
        A B R) ≠ (nb082AlphaDummy027 A B R) from (by
          unfold
            nb082AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy028 A B R p)
        from (by
          unfold
            nb082AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠
        (nb082AlphaDummy025 A B R) from (by
          unfold
            nb082AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy026 A B R p)
        from (by
          unfold
            nb082AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠ (nb082AlphaDummy027 A B R)
        from (by
          unfold
            nb082AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy028 A B R p)
        from (by
          unfold
            nb082AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy025 A B R) from (by
          unfold
            nb082AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy026 A B R p)
        from (by
          unfold
            nb082AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021
        A B R) ≠ (nb082AlphaDummy027 A B R) from (by
          unfold
            nb082AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy028 A B R p)
        from (by
          unfold
            nb082AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠
        (nb082AlphaDummy025 A B R) from (by
          unfold
            nb082AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy026 A B R p)
        from (by
          unfold
            nb082AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy021 A B R), (nb082AlphaDummy024 A B R p)),
        ((nb082AlphaDummy020 A B R), (nb082AlphaDummy023 A B R p)),
        ((nb082AlphaDummy019 A B R), (nb082AlphaDummy022 A B R p)),
        ((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy011 A B R), (nb082AlphaDummy012 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015
        A B R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020
        A B R) ≠ (nb082AlphaDummy031 A B R) from (by
          unfold
            nb082AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy032 A B R p)
        from (by
          unfold
            nb082AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy029 A B R) from (by
          unfold
            nb082AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy030 A B R p)
        from (by
          unfold
            nb082AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020
        A B R) ≠ (nb082AlphaDummy031 A B R) from (by
          unfold
            nb082AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy032 A B R p)
        from (by
          unfold
            nb082AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy029 A B R) from (by
          unfold
            nb082AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy030 A B R p)
        from (by
          unfold
            nb082AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠ (nb082AlphaDummy033 A B R)
        from (by
          unfold
            nb082AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy034 A B R p)
        from (by
          unfold
            nb082AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠
        (nb082AlphaDummy029 A B R) from (by
          unfold
            nb082AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy030 A B R p)
        from (by
          unfold
            nb082AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021
        A B R) ≠ (nb082AlphaDummy033 A B R) from (by
          unfold
            nb082AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy034 A B R p)
        from (by
          unfold
            nb082AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠
        (nb082AlphaDummy029 A B R) from (by
          unfold
            nb082AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy030 A B R p)
        from (by
          unfold
            nb082AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B
                    R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy011 A B R), (nb082AlphaDummy012 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082AlphaDummy013 A B R) ≠ (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B
                    R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy011 A B R), (nb082AlphaDummy012 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb082AlphaDummy000 A B R) ≠ (nb082AlphaDummy006 A B R)
                                  from (by
                                    unfold nb082AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb082_support_mem_0006 A B R)
                                            1)))) (show p ≠ (nb082AlphaDummy008 A B R p) from
                                  (by
                                    unfold nb082AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb082_support_mem_0008 A B R p) 1))))
                                (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
                                      (nb082AlphaDummy005 A B R) from (by
                                      unfold nb082AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0006 A B R) 0))))
                                  (show p ≠ (nb082AlphaDummy007 A B R p) from (by
                                      unfold nb082AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb082_support_mem_0008 A B R p) 0))))
                                  (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
                                        (nb082AlphaDummy011 A B R) from (by
                                        unfold nb082AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0010 A B R) 0))))
                                    (show p ≠ (nb082AlphaDummy012 A B R p) from (by
                                        unfold nb082AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb082_support_mem_0011 A B R p) 0))))
                                    (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy009 A B R) from (by
                                          unfold nb082AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0007 A B R) 0))))
                                      (show p ≠ (nb082AlphaDummy010 A B R p) from (by
                                          unfold nb082AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb082_support_mem_0009 A B R p) 0))))
                                      (TAlphaVar.there (show (nb082AlphaDummy000 A B R) ≠
        (nb082AlphaDummy001 A B R) from (by
          unfold nb082AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0004 A B R) 0))))
                                        (show p ≠ (nb082AlphaDummy002 A B R p) from (by
          unfold nb082AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0005 A B R p) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective
                                  (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
                                    ((Class.cv (nb082AlphaDummy001 A B R))).fv) (by decide))
                                (freshVar_injective (((Class.cv p)).fv ∪
                                    ((Class.cv (nb082AlphaDummy002 A B R p))).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy013 A B R) from (by
          unfold nb082AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 0)))) (show (nb082AlphaDummy008 A B R p) ≠
        (nb082AlphaDummy015 A B R p) from (by
          unfold nb082AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p) 0)))) (TAlphaVar.there (show
        (nb082AlphaDummy006 A B R) ≠ (nb082AlphaDummy014 A B R) from (by
          unfold nb082AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R) 1)))) (show (nb082AlphaDummy008 A B R p) ≠
        (nb082AlphaDummy016 A B R p) from (by
          unfold nb082AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                                      (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb082AlphaDummy006 A B R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082AlphaDummy008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082AlphaDummy013 A B R) ≠ (nb082AlphaDummy020 A B R) from (by
          unfold
            nb082AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  1)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy023 A B R p)
        from (by
          unfold
            nb082AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  1)))) (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy019 A B R) from (by
          unfold
            nb082AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0016
                    A B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy022 A B R p)
        from (by
          unfold
            nb082AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0017
                    A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold
            nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014
                    A B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold
            nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015
                    A B R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy021 A B R), (nb082AlphaDummy024 A B R p)),
        ((nb082AlphaDummy020 A B R), (nb082AlphaDummy023 A B R p)),
        ((nb082AlphaDummy019 A B R), (nb082AlphaDummy022 A B R p)),
        ((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy011 A B R), (nb082AlphaDummy012 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy027 A B R) from (by
          unfold
            nb082AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy028 A B R p)
        from (by
          unfold
            nb082AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy025 A B R) from (by
          unfold
            nb082AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy026 A B R p)
        from (by
          unfold
            nb082AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021
        A B R) ≠ (nb082AlphaDummy027 A B R) from (by
          unfold
            nb082AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy028 A B R p)
        from (by
          unfold
            nb082AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠
        (nb082AlphaDummy025 A B R) from (by
          unfold
            nb082AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy026 A B R p)
        from (by
          unfold
            nb082AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠ (nb082AlphaDummy027 A B R)
        from (by
          unfold
            nb082AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy028 A B R p)
        from (by
          unfold
            nb082AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0021
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy025 A B R) from (by
          unfold
            nb082AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy026 A B R p)
        from (by
          unfold
            nb082AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0019
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021
        A B R) ≠ (nb082AlphaDummy027 A B R) from (by
          unfold
            nb082AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy028 A B R p)
        from (by
          unfold
            nb082AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0025
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠
        (nb082AlphaDummy025 A B R) from (by
          unfold
            nb082AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy026 A B R p)
        from (by
          unfold
            nb082AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0023
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy021 A B R), (nb082AlphaDummy024 A B R p)),
        ((nb082AlphaDummy020 A B R), (nb082AlphaDummy023 A B R p)),
        ((nb082AlphaDummy019 A B R), (nb082AlphaDummy022 A B R p)),
        ((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy011 A B R), (nb082AlphaDummy012 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015
        A B R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020
        A B R) ≠ (nb082AlphaDummy031 A B R) from (by
          unfold
            nb082AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy032 A B R p)
        from (by
          unfold
            nb082AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy029 A B R) from (by
          unfold
            nb082AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy030 A B R p)
        from (by
          unfold
            nb082AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020
        A B R) ≠ (nb082AlphaDummy031 A B R) from (by
          unfold
            nb082AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy032 A B R p)
        from (by
          unfold
            nb082AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0029
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy029 A B R) from (by
          unfold
            nb082AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy023 A B R p) ≠ (nb082AlphaDummy030 A B R p)
        from (by
          unfold
            nb082AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0027
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb082AlphaDummy013
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠ (nb082AlphaDummy033 A B R)
        from (by
          unfold
            nb082AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy034 A B R p)
        from (by
          unfold
            nb082AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠
        (nb082AlphaDummy029 A B R) from (by
          unfold
            nb082AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy030 A B R p)
        from (by
          unfold
            nb082AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021
        A B R) ≠ (nb082AlphaDummy033 A B R) from (by
          unfold
            nb082AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy034 A B R p)
        from (by
          unfold
            nb082AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0033
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy021 A B R) ≠
        (nb082AlphaDummy029 A B R) from (by
          unfold
            nb082AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb082AlphaDummy024 A B R p) ≠ (nb082AlphaDummy030 A B R p)
        from (by
          unfold
            nb082AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0031
                    A
                    B
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B
                    R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy011 A B R), (nb082AlphaDummy012 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082AlphaDummy013 A B R) ≠ (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A B
                    R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A B
                    R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy011 A B R), (nb082AlphaDummy012 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb082SplitAlpha0001 A B R p)))))))))

theorem nb082_focused_notmem_0000 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪ ((synCxpk B B)).fv ∪
          ((synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxpk B B]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_wpp_notmem_0106 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∉ ((synCxpk B B)).fv := by
  simpa only [nb082AlphaDummy001, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0000 A B R) (nb082_focused_notmem_0000 A B R))

theorem nb082_focused_notmem_0001 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy002 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((synCxpk B B)).fv ∪ ((synCfdminvalp R A B (Class.cv p))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxpk B B]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_wpp_notmem_0107 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy002 A B R p) ∉ ((synCxpk B B)).fv := by
  simpa only [nb082AlphaDummy002, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0001 A B R p) (nb082_focused_notmem_0001 A B R p))

theorem nb082_focused_notmem_0002 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb082_wpp_notmem_0108 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∉ ((synCxpk B B)).fv := by
  simpa only [nb082AlphaDummy000, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0002 A B R) (nb082_focused_notmem_0002 A B R))

theorem nb082_wpp_notmem_0109 (B : Class) (p : Var) (dv_B_p : p ∉ B.fv) :
    p ∉ ((synCxpk B B)).fv := by
  simpa only [fv_syn_cxpk, Finset.mem_union, not_or] using (And.intro dv_B_p dv_B_p)

theorem nb082_focused_notmem_0003 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy003 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪
            ({(nb082AlphaDummy001 A B R)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
              (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
                (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
      (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
        (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxpk B B]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_wpp_notmem_0110 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy003 A B R) ∉ ((synCxpk B B)).fv := by
  simpa only [nb082AlphaDummy003, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0003 A B R) (nb082_focused_notmem_0003 A B R))

theorem nb082_focused_notmem_0004 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy004 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb082AlphaDummy002 A B R p)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv p) (synCxpk B B))
              (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
                (synCfdminvalp R A B (Class.cv p))))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (synCxpk B B))
      (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
        (synCfdminvalp R A B (Class.cv p)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv p) (synCxpk B B)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxpk B B]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_wpp_notmem_0111 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy004 A B R p) ∉ ((synCxpk B B)).fv := by
  simpa only [nb082AlphaDummy004, fv_syn_cxpk, Finset.mem_union, not_or] using
    (And.intro (nb082_focused_notmem_0004 A B R p) (nb082_focused_notmem_0004 A B R p))

theorem nb082_compact_envfresh_0007 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_B_p : p ∉ B.fv) :
    TEnvFresh
      [((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p),
        ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
      ((synCxpk B B)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb082AlphaDummy001 A B R) (nb082AlphaDummy002 A B R p)
      (nb082_wpp_notmem_0106 A B R) (nb082_wpp_notmem_0107 A B R p)
      (TEnvFresh.consFresh (nb082AlphaDummy000 A B R) p (nb082_wpp_notmem_0108 A B R)
        (nb082_wpp_notmem_0109 B p dv_B_p)
        (TEnvFresh.consFresh (nb082AlphaDummy003 A B R) (nb082AlphaDummy004 A B R p)
          (nb082_wpp_notmem_0110 A B R) (nb082_wpp_notmem_0111 A B R p)
          (TEnvFresh.nil ((synCxpk B B)).fv))))

/-- Checked nominal proof certificate identified upstream as `nb082_wpp_refl_0007`. -/
@[expose]
noncomputable def nb082WppRefl0007 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_B_p : p ∉ B.fv) :
    TReflOn
      [((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p),
        ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
      ((synCxpk B B)).fv :=
  TEnvFresh.reflOn (nb082_compact_envfresh_0007 A B R p dv_B_p)

theorem nb082_focused_notmem_0005 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((synCcnvk (synCfdminsep R A B))).fv ∪
          ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv)
        1 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0006 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((synCcnvk (synCfdminsep R A B))).fv ∪
          ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv)
        1 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0007 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCcnvk (synCfdminsep R A B))).fv ∪
          ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0112 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy050 A B R) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy050, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0005 A B R) (nb082_focused_notmem_0006 A B R))
      (nb082_focused_notmem_0007 A B R))

theorem nb082_focused_notmem_0008 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∉ A.fv :=
  by
  change
    freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 1 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0009 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∉ B.fv :=
  by
  change
    freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 1 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0010 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∉ R.fv :=
  by
  change
    freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0113 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy052 A B R p) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy052, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0008 A B R p) (nb082_focused_notmem_0009 A B R p))
      (nb082_focused_notmem_0010 A B R p))

theorem nb082_focused_notmem_0011 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((synCcnvk (synCfdminsep R A B))).fv ∪
          ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0012 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((synCcnvk (synCfdminsep R A B))).fv ∪
          ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0013 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCcnvk (synCfdminsep R A B))).fv ∪
          ((synCsn (Class.cv (nb082AlphaDummy000 A B R)))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0114 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy049 A B R) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy049, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0011 A B R) (nb082_focused_notmem_0012 A B R))
      (nb082_focused_notmem_0013 A B R))

theorem nb082_focused_notmem_0014 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∉ A.fv :=
  by
  change
    freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0015 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∉ B.fv :=
  by
  change
    freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0016 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∉ R.fv :=
  by
  change
    freshVar (((synCcnvk (synCfdminsep R A B))).fv ∪ ((synCsn (Class.cv p))).fv) 0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0115 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy051 A B R p) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy051, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0014 A B R p) (nb082_focused_notmem_0015 A B R p))
      (nb082_focused_notmem_0016 A B R p))

theorem nb082_focused_notmem_0017 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy047 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R))))).fv ∪ ((synC1c)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0018 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy047 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R))))).fv ∪ ((synC1c)).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0019 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy047 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R))))).fv ∪ ((synC1c)).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0116 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy047 A B R) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy047, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0017 A B R) (nb082_focused_notmem_0018 A B R))
      (nb082_focused_notmem_0019 A B R))

theorem nb082_focused_notmem_0020 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy048 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (((synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))).fv ∪
          ((synC1c)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0021 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy048 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (((synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))).fv ∪
          ((synC1c)).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0022 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy048 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))).fv ∪
          ((synC1c)).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0117 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy048 A B R p) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy048, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0020 A B R p) (nb082_focused_notmem_0021 A B R p))
      (nb082_focused_notmem_0022 A B R p))

theorem nb082_focused_notmem_0023 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy045 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((synCnin (synCimak (synCcnvk (synCfdminsep R A B))
                (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv ∪ ((synCnin
              (synCimak (synCcnvk (synCfdminsep R A B))
                (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (synCimak (synCcnvk (synCfdminsep R A B))
        (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0024 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy045 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((synCnin (synCimak (synCcnvk (synCfdminsep R A B))
                (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv ∪ ((synCnin
              (synCimak (synCcnvk (synCfdminsep R A B))
                (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (synCimak (synCcnvk (synCfdminsep R A B))
        (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0025 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy045 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin (synCimak (synCcnvk (synCfdminsep R A B))
                (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv ∪ ((synCnin
              (synCimak (synCcnvk (synCfdminsep R A B))
                (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin
      (synCimak (synCcnvk (synCfdminsep R A B))
        (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0118 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy045 A B R) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy045, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0023 A B R) (nb082_focused_notmem_0024 A B R))
      (nb082_focused_notmem_0025 A B R))

theorem nb082_focused_notmem_0026 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy046 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
              (synC1c))).fv ∪
          ((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
              (synC1c))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0027 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy046 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
              (synC1c))).fv ∪
          ((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
              (synC1c))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0028 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy046 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
              (synC1c))).fv ∪
          ((synCnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
              (synC1c))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0119 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy046 A B R p) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy046, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0026 A B R p) (nb082_focused_notmem_0027 A B R p))
      (nb082_focused_notmem_0028 A B R p))

theorem nb082_focused_notmem_0029 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy042 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
        1 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin
      (synCimak (synCcnvk (synCfdminsep R A B))
        (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0030 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy042 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
        1 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin
      (synCimak (synCcnvk (synCfdminsep R A B))
        (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0031 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy042 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin
      (synCimak (synCcnvk (synCfdminsep R A B))
        (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0120 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy042 A B R) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy042, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0029 A B R) (nb082_focused_notmem_0030 A B R))
      (nb082_focused_notmem_0031 A B R))

theorem nb082_focused_notmem_0032 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy044 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv)
        1 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0033 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy044 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv)
        1 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0034 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy044 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_syn_cin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0121 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy044 A B R p) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy044, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0032 A B R p) (nb082_focused_notmem_0033 A B R p))
      (nb082_focused_notmem_0034 A B R p))

theorem nb082_focused_notmem_0035 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy041 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin
      (synCimak (synCcnvk (synCfdminsep R A B))
        (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0036 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy041 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin
      (synCimak (synCcnvk (synCfdminsep R A B))
        (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0037 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy041 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B))
              (synCsn (Class.cv (nb082AlphaDummy000 A B R)))) (synC1c))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin
      (synCimak (synCcnvk (synCfdminsep R A B))
        (synCsn (Class.cv (nb082AlphaDummy000 A B R))))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B))
      (synCsn (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0122 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy041 A B R) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy041, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0035 A B R) (nb082_focused_notmem_0036 A B R))
      (nb082_focused_notmem_0037 A B R))

theorem nb082_focused_notmem_0038 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy043 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
