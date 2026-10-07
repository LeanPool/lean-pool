/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C082C001Block001

/-! NF weak partition development: NAR4C082C001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb082_split_alpha_0000`. -/
@[expose]
noncomputable def nb082SplitAlpha0000 (A : Class) (B : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p),
        ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
      (Wff.neg (Wff.classMem (Class.cv (nb082AlphaDummy035 A B R))
          (Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy001 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                  (synCsn (synC0c))))))))
      (Wff.neg (Wff.classMem (Class.cv (nb082AlphaDummy036 A B R p))
          (Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
              (Class.cv (nb082AlphaDummy002 A B R p))
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                  (synCsn (synC0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy006 A B R) from (by
                      unfold nb082AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb082_support_mem_0034 A B R) 1))))
                  (show (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy008 A B R p) from
                    (by
                      unfold nb082AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 1))))
                  (TAlphaVar.there
                    (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy005 A B R) from (by
                        unfold nb082AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb082_support_mem_0034 A B R) 0)))) (show
                      (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy007 A B R p) from (by
                        unfold nb082AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 0))))
                    (TAlphaVar.there
                      (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy035 A B R) from
                        (by
                          unfold nb082AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0038 A B R) 0)))) (show
                        (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy036 A B R p) from
                        (by
                          unfold nb082AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0039 A B R p) 0))))
                      (TAlphaVar.there (show
                          (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy009 A B R) from (by
                            unfold nb082AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb082_support_mem_0035 A B R) 0)))) (show
                          (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy010 A B R p) from
                          (by
                            unfold nb082AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb082_support_mem_0037 A B R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
                      ((Class.cv (nb082AlphaDummy001 A B R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb082_support_mem_0013 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy014 A B R) from (by
          unfold nb082AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R)
                  1)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy016 A B R p)
        from (by
          unfold nb082AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy039 A B R) from (by
          unfold nb082AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0042 A B R)
                  0)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy040 A B R p)
        from (by
          unfold nb082AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0043 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy037 A B R) from (by
          unfold nb082AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0040 A B R)
                  0)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy038 A B R p)
        from (by
          unfold nb082AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0041 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy006 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb082AlphaDummy008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
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
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082AlphaDummy020 A B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A
        B R) ≠ (nb082AlphaDummy031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy033 A B R) from (by
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
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb082_support_mem_0013 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy014 A B R) from (by
          unfold nb082AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R)
                  1)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy016 A B R p)
        from (by
          unfold nb082AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy039 A B R) from (by
          unfold nb082AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0042 A B R)
                  0)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy040 A B R p)
        from (by
          unfold nb082AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0043 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy037 A B R) from (by
          unfold nb082AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0040 A B R)
                  0)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy038 A B R p)
        from (by
          unfold nb082AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0041 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy006 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb082AlphaDummy008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
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
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082AlphaDummy020 A B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A
        B R) ≠ (nb082AlphaDummy031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy033 A B R) from (by
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
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
                          ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
                          ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
                          ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
                          ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
                          ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
                          ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
                            (nb082AlphaDummy004 A B R p))] (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb082_split_alpha_0001`. -/
@[expose]
noncomputable def nb082SplitAlpha0001 (A : Class) (B : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p),
        ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb082AlphaDummy035 A B R))
          (Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
              (Class.cv (nb082AlphaDummy001 A B R))
              (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb082AlphaDummy035 A B R))
            (Class.cab (nb082AlphaDummy005 A B R) (synWrex (nb082AlphaDummy006 A B R)
                (Class.cv (nb082AlphaDummy001 A B R))
                (Wff.classEq (Class.cv (nb082AlphaDummy005 A B R))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy006 A B R)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb082AlphaDummy036 A B R p))
          (Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
              (Class.cv (nb082AlphaDummy002 A B R p))
              (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb082AlphaDummy036 A B R p))
            (Class.cab (nb082AlphaDummy007 A B R p) (synWrex (nb082AlphaDummy008 A B R p)
                (Class.cv (nb082AlphaDummy002 A B R p))
                (Wff.classEq (Class.cv (nb082AlphaDummy007 A B R p))
                  (synCun (synCphi (Class.cv (nb082AlphaDummy008 A B R p)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy006 A B R) from (by
                      unfold nb082AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb082_support_mem_0034 A B R) 1))))
                  (show (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy008 A B R p) from
                    (by
                      unfold nb082AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 1))))
                  (TAlphaVar.there
                    (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy005 A B R) from (by
                        unfold nb082AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb082_support_mem_0034 A B R) 0)))) (show
                      (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy007 A B R p) from (by
                        unfold nb082AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb082_support_mem_0036 A B R p) 0))))
                    (TAlphaVar.there
                      (show (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy035 A B R) from
                        (by
                          unfold nb082AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0038 A B R) 0)))) (show
                        (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy036 A B R p) from
                        (by
                          unfold nb082AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb082_support_mem_0039 A B R p) 0))))
                      (TAlphaVar.there (show
                          (nb082AlphaDummy001 A B R) ≠ (nb082AlphaDummy009 A B R) from (by
                            unfold nb082AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb082_support_mem_0035 A B R) 0)))) (show
                          (nb082AlphaDummy002 A B R p) ≠ (nb082AlphaDummy010 A B R p) from
                          (by
                            unfold nb082AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb082_support_mem_0037 A B R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb082AlphaDummy000 A B R))).fv ∪
                      ((Class.cv (nb082AlphaDummy001 A B R))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv p)).fv ∪ ((Class.cv (nb082AlphaDummy002 A B R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb082_support_mem_0013 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy014 A B R) from (by
          unfold nb082AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R)
                  1)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy016 A B R p)
        from (by
          unfold nb082AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy039 A B R) from (by
          unfold nb082AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0042 A B R)
                  0)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy040 A B R p)
        from (by
          unfold nb082AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0043 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy037 A B R) from (by
          unfold nb082AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0040 A B R)
                  0)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy038 A B R p)
        from (by
          unfold nb082AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0041 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy006 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb082AlphaDummy008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
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
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082AlphaDummy020 A B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A
        B R) ≠ (nb082AlphaDummy031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy033 A B R) from (by
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
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb082_support_mem_0013 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy014 A B R) from (by
          unfold nb082AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0012 A B R)
                  1)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy016 A B R p)
        from (by
          unfold nb082AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0013 A B R p)
                  1)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy039 A B R) from (by
          unfold nb082AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0042 A B R)
                  0)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy040 A B R p)
        from (by
          unfold nb082AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0043 A B R p)
                  0)))) (TAlphaVar.there (show (nb082AlphaDummy006 A B R) ≠
        (nb082AlphaDummy037 A B R) from (by
          unfold nb082AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0040 A B R)
                  0)))) (show (nb082AlphaDummy008 A B R p) ≠ (nb082AlphaDummy038 A B R p)
        from (by
          unfold nb082AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0041 A B R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy006 A B R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb082AlphaDummy008 A B R p))).fv) (by decide)) (TAlphaVar.here _ _ _)))
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
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb082AlphaDummy020 A B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy027 A B R) from (by
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
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb082AlphaDummy013 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb082AlphaDummy015 A B R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A B R) ≠
        (nb082AlphaDummy031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy020 A
        B R) ≠ (nb082AlphaDummy031 A B R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy021 A
        B R) ≠ (nb082AlphaDummy033 A B R) from (by
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
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb082AlphaDummy013 A B R) ≠
        (nb082AlphaDummy017 A B R) from (by
          unfold nb082AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0014 A
                    B R)
                  0)))) (show (nb082AlphaDummy015 A B R p) ≠ (nb082AlphaDummy018 A B R p)
        from (by
          unfold nb082AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb082_support_mem_0015 A
                    B R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb082AlphaDummy017 A B R), (nb082AlphaDummy018 A B R p)),
        ((nb082AlphaDummy013 A B R), (nb082AlphaDummy015 A B R p)),
        ((nb082AlphaDummy014 A B R), (nb082AlphaDummy016 A B R p)),
        ((nb082AlphaDummy039 A B R), (nb082AlphaDummy040 A B R p)),
        ((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
        ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
        ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
        ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
        ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
        (nb082AlphaDummy004 A B R p))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb082AlphaDummy037 A B R), (nb082AlphaDummy038 A B R p)),
                          ((nb082AlphaDummy006 A B R), (nb082AlphaDummy008 A B R p)),
                          ((nb082AlphaDummy005 A B R), (nb082AlphaDummy007 A B R p)),
                          ((nb082AlphaDummy035 A B R), (nb082AlphaDummy036 A B R p)),
                          ((nb082AlphaDummy009 A B R), (nb082AlphaDummy010 A B R p)),
                          ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
                          ((nb082AlphaDummy000 A B R), p), ((nb082AlphaDummy003 A B R),
                            (nb082AlphaDummy004 A B R p))] (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb082SplitAlpha0000 A B R p))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
