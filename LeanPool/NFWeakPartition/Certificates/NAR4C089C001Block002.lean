/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C089C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C089C001Part004`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb089_split_alpha_0000`. -/
@[expose]
noncomputable def nb089SplitAlpha0000 (u : Var) (A : Class) (B : Class) (R : Class) :
    TAlphaWff
      [((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u),
        ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
        ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      (Wff.imp (Wff.classMem (Class.cv (nb089AlphaDummy008 A B R))
          (Class.cv (nb089AlphaDummy003 A B R))) (Wff.neg
          (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
            (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb089AlphaDummy010 u A B R))
          (Class.cv (nb089AlphaDummy004 u A B R))) (Wff.neg
          (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
            (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb089AlphaDummy003 A B R) ≠ (nb089AlphaDummy008 A B R) from (by
              unfold nb089AlphaDummy008;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 1))))
          (show (nb089AlphaDummy004 u A B R) ≠ (nb089AlphaDummy010 u A B R) from (by
              unfold nb089AlphaDummy010;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 1))))
          (TAlphaVar.there
            (show (nb089AlphaDummy003 A B R) ≠ (nb089AlphaDummy007 A B R) from (by
                unfold nb089AlphaDummy007;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 0))))
            (show (nb089AlphaDummy004 u A B R) ≠ (nb089AlphaDummy009 u A B R) from (by
                unfold nb089AlphaDummy009;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 0))))
            (TAlphaVar.there
              (show (nb089AlphaDummy003 A B R) ≠ (nb089AlphaDummy037 A B R) from (by
                  unfold nb089AlphaDummy037;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0038 A B R) 0))))
              (show (nb089AlphaDummy004 u A B R) ≠ (nb089AlphaDummy038 u A B R) from (by
                  unfold nb089AlphaDummy038;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb089_support_mem_0039 u A B R) 0)))) (TAlphaVar.there
                (show (nb089AlphaDummy003 A B R) ≠ (nb089AlphaDummy011 A B R) from (by
                    unfold nb089AlphaDummy011;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb089_support_mem_0035 A B R) 0))))
                (show (nb089AlphaDummy004 u A B R) ≠ (nb089AlphaDummy012 u A B R) from (by
                    unfold nb089AlphaDummy012;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb089_support_mem_0037 u A B R) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
                ((Class.cv (nb089AlphaDummy003 A B R))).fv) (by decide)) (freshVar_injective
              (((Class.cv u)).fv ∪ ((Class.cv (nb089AlphaDummy004 u A B R))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089AlphaDummy008 A B R) ≠
                                        (nb089AlphaDummy015 A B R) from (by
                                        unfold nb089AlphaDummy015;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0012 A B R) 0)))) (show
                                      (nb089AlphaDummy010 u A B R) ≠
                                        (nb089AlphaDummy017 u A B R) from (by
                                        unfold nb089AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0013 u A B R) 0))))
                                    (TAlphaVar.there (show (nb089AlphaDummy008 A B R) ≠
        (nb089AlphaDummy016 A B R) from (by
                                          unfold nb089AlphaDummy016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0012 A B R) 1)))) (show
                                        (nb089AlphaDummy010 u A B R) ≠
        (nb089AlphaDummy018 u A B R) from (by
                                          unfold nb089AlphaDummy018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0013 u A B R) 1))))
                                      (TAlphaVar.there (show (nb089AlphaDummy008 A B R) ≠
        (nb089AlphaDummy041 A B R) from (by
          unfold nb089AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0042 A B R) 0)))) (show (nb089AlphaDummy010 u A B R) ≠
        (nb089AlphaDummy042 u A B R) from (by
          unfold nb089AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0043 u A B R) 0)))) (TAlphaVar.there (show
        (nb089AlphaDummy008 A B R) ≠ (nb089AlphaDummy039 A B R) from (by
          unfold nb089AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0040 A B R) 0)))) (show (nb089AlphaDummy010 u A B R) ≠
        (nb089AlphaDummy040 u A B R) from (by
          unfold nb089AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0041 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb089AlphaDummy008 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb089AlphaDummy010 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy022 A B R)
        from (by
          unfold nb089AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  1)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy025 u A B R)
        from (by
          unfold nb089AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy021 A B R) from (by
          unfold nb089AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy024 u A B R)
        from (by
          unfold nb089AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold
            nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014
                    A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold
            nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy023 A B R), (nb089AlphaDummy026 u A B R)),
        ((nb089AlphaDummy022 A B R), (nb089AlphaDummy025 u A B R)),
        ((nb089AlphaDummy021 A B R), (nb089AlphaDummy024 u A B R)),
        ((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy041 A B R), (nb089AlphaDummy042 u A B R)),
        ((nb089AlphaDummy039 A B R), (nb089AlphaDummy040 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠ (nb089AlphaDummy029 A B R)
        from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy023 A B R), (nb089AlphaDummy026 u A B R)),
        ((nb089AlphaDummy022 A B R), (nb089AlphaDummy025 u A B R)),
        ((nb089AlphaDummy021 A B R), (nb089AlphaDummy024 u A B R)),
        ((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy041 A B R), (nb089AlphaDummy042 u A B R)),
        ((nb089AlphaDummy039 A B R), (nb089AlphaDummy040 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017
        u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠ (nb089AlphaDummy033 A B R)
        from (by
          unfold
            nb089AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy034 u A B R)
        from (by
          unfold
            nb089AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy022
        A B R) ≠ (nb089AlphaDummy033 A B R) from (by
          unfold
            nb089AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy034 u A B R)
        from (by
          unfold
            nb089AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠ (nb089AlphaDummy035 A B R)
        from (by
          unfold
            nb089AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy036 u A B R)
        from (by
          unfold
            nb089AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy035 A B R) from (by
          unfold
            nb089AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy036 u A B R)
        from (by
          unfold
            nb089AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy041 A B R), (nb089AlphaDummy042 u A B R)),
        ((nb089AlphaDummy039 A B R), (nb089AlphaDummy040 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy019 A B R)
        from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy041 A B R), (nb089AlphaDummy042 u A B R)),
        ((nb089AlphaDummy039 A B R), (nb089AlphaDummy040 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089AlphaDummy008 A B R) ≠
                                        (nb089AlphaDummy015 A B R) from (by
                                        unfold nb089AlphaDummy015;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0012 A B R) 0)))) (show
                                      (nb089AlphaDummy010 u A B R) ≠
                                        (nb089AlphaDummy017 u A B R) from (by
                                        unfold nb089AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0013 u A B R) 0))))
                                    (TAlphaVar.there (show (nb089AlphaDummy008 A B R) ≠
        (nb089AlphaDummy016 A B R) from (by
                                          unfold nb089AlphaDummy016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0012 A B R) 1)))) (show
                                        (nb089AlphaDummy010 u A B R) ≠
        (nb089AlphaDummy018 u A B R) from (by
                                          unfold nb089AlphaDummy018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0013 u A B R) 1))))
                                      (TAlphaVar.there (show (nb089AlphaDummy008 A B R) ≠
        (nb089AlphaDummy041 A B R) from (by
          unfold nb089AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0042 A B R) 0)))) (show (nb089AlphaDummy010 u A B R) ≠
        (nb089AlphaDummy042 u A B R) from (by
          unfold nb089AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0043 u A B R) 0)))) (TAlphaVar.there (show
        (nb089AlphaDummy008 A B R) ≠ (nb089AlphaDummy039 A B R) from (by
          unfold nb089AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0040 A B R) 0)))) (show (nb089AlphaDummy010 u A B R) ≠
        (nb089AlphaDummy040 u A B R) from (by
          unfold nb089AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0041 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb089AlphaDummy008 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb089AlphaDummy010 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy022 A B R)
        from (by
          unfold nb089AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  1)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy025 u A B R)
        from (by
          unfold nb089AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy021 A B R) from (by
          unfold nb089AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy024 u A B R)
        from (by
          unfold nb089AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold
            nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014
                    A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold
            nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy023 A B R), (nb089AlphaDummy026 u A B R)),
        ((nb089AlphaDummy022 A B R), (nb089AlphaDummy025 u A B R)),
        ((nb089AlphaDummy021 A B R), (nb089AlphaDummy024 u A B R)),
        ((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy041 A B R), (nb089AlphaDummy042 u A B R)),
        ((nb089AlphaDummy039 A B R), (nb089AlphaDummy040 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠ (nb089AlphaDummy029 A B R)
        from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy023 A B R), (nb089AlphaDummy026 u A B R)),
        ((nb089AlphaDummy022 A B R), (nb089AlphaDummy025 u A B R)),
        ((nb089AlphaDummy021 A B R), (nb089AlphaDummy024 u A B R)),
        ((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy041 A B R), (nb089AlphaDummy042 u A B R)),
        ((nb089AlphaDummy039 A B R), (nb089AlphaDummy040 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017
        u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠ (nb089AlphaDummy033 A B R)
        from (by
          unfold
            nb089AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy034 u A B R)
        from (by
          unfold
            nb089AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy022
        A B R) ≠ (nb089AlphaDummy033 A B R) from (by
          unfold
            nb089AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy034 u A B R)
        from (by
          unfold
            nb089AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠ (nb089AlphaDummy035 A B R)
        from (by
          unfold
            nb089AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy036 u A B R)
        from (by
          unfold
            nb089AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy035 A B R) from (by
          unfold
            nb089AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy036 u A B R)
        from (by
          unfold
            nb089AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy041 A B R), (nb089AlphaDummy042 u A B R)),
        ((nb089AlphaDummy039 A B R), (nb089AlphaDummy040 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy019 A B R)
        from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy041 A B R), (nb089AlphaDummy042 u A B R)),
        ((nb089AlphaDummy039 A B R), (nb089AlphaDummy040 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb089AlphaDummy039 A B R), (nb089AlphaDummy040 u A B R)),
                    ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
                    ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
                    ((nb089AlphaDummy037 A B R), (nb089AlphaDummy038 u A B R)),
                    ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
                    ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
                    ((nb089AlphaDummy000 A B R), u),
                    ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
                    ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C089C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb089_split_alpha_0001`. -/
@[expose]
noncomputable def nb089SplitAlpha0001 (u : Var) (A : Class) (B : Class) (R : Class) :
    TAlphaWff
      [((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u),
        ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
        ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      (Wff.imp (Wff.classMem (Class.cv (nb089AlphaDummy011 A B R)) (synCcompl
            (Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
                (Class.cv (nb089AlphaDummy000 A B R))
                (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy008 A B R)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb089AlphaDummy011 A B R)) (synCcompl
              (Class.cab (nb089AlphaDummy007 A B R) (synWrex (nb089AlphaDummy008 A B R)
                  (Class.cv (nb089AlphaDummy003 A B R))
                  (Wff.classEq (Class.cv (nb089AlphaDummy007 A B R))
                    (synCun (synCphi (Class.cv (nb089AlphaDummy008 A B R)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb089AlphaDummy012 u A B R)) (synCcompl
            (Class.cab (nb089AlphaDummy009 u A B R)
              (synWrex (nb089AlphaDummy010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb089AlphaDummy012 u A B R)) (synCcompl
              (Class.cab (nb089AlphaDummy009 u A B R)
                (synWrex (nb089AlphaDummy010 u A B R)
                  (Class.cv (nb089AlphaDummy004 u A B R))
                  (Wff.classEq (Class.cv (nb089AlphaDummy009 u A B R))
                    (synCun (synCphi (Class.cv (nb089AlphaDummy010 u A B R)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show
                            (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy008 A B R) from
                            (by
                              unfold nb089AlphaDummy008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))))
                          (show u ≠ (nb089AlphaDummy010 u A B R) from (by
                              unfold nb089AlphaDummy010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0008 u A B R)
                                      1)))) (TAlphaVar.there (show
                              (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy007 A B R) from
                              (by
                                unfold nb089AlphaDummy007;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0006 A B R)
                                        0)))) (show u ≠ (nb089AlphaDummy009 u A B R) from (by
                                unfold nb089AlphaDummy009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0008 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy013 A B R)
                                from (by
                                  unfold nb089AlphaDummy013;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0010 A B R)
                                          0)))) (show u ≠ (nb089AlphaDummy014 u A B R) from
                                (by
                                  unfold nb089AlphaDummy014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0011 u A B R)
                                          0)))) (TAlphaVar.there (show
                                  (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy011 A B R)
                                  from (by
                                    unfold nb089AlphaDummy011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb089_support_mem_0007 A B R)
                                            0)))) (show u ≠ (nb089AlphaDummy012 u A B R) from
                                  (by
                                    unfold nb089AlphaDummy012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb089_support_mem_0009 u A B R) 0))))
                                (TAlphaVar.there (show (nb089AlphaDummy000 A B R) ≠
                                      (nb089AlphaDummy003 A B R) from (by
                                      unfold nb089AlphaDummy003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0004 A B R) 0))))
                                  (show u ≠ (nb089AlphaDummy004 u A B R) from (by
                                      unfold nb089AlphaDummy004;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0005 u A B R) 0))))
                                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
                              ((Class.cv (nb089AlphaDummy003 A B R))).fv) (by decide))
                          (freshVar_injective (((Class.cv u)).fv ∪
                              ((Class.cv (nb089AlphaDummy004 u A B R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb089AlphaDummy008 A B R) ≠
                                      (nb089AlphaDummy015 A B R) from (by
                                      unfold nb089AlphaDummy015;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0012 A B R) 0)))) (show
                                    (nb089AlphaDummy010 u A B R) ≠
                                      (nb089AlphaDummy017 u A B R) from (by
                                      unfold nb089AlphaDummy017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0013 u A B R) 0))))
                                  (TAlphaVar.there (show (nb089AlphaDummy008 A B R) ≠
                                        (nb089AlphaDummy016 A B R) from (by
                                        unfold nb089AlphaDummy016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0012 A B R) 1)))) (show
                                      (nb089AlphaDummy010 u A B R) ≠
                                        (nb089AlphaDummy018 u A B R) from (by
                                        unfold nb089AlphaDummy018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0013 u A B R) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb089AlphaDummy008 A B R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb089AlphaDummy010 u A B R))).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy022 A B R) from (by
          unfold nb089AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016 A
                    B R)
                  1)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy025 u A B R)
        from (by
          unfold nb089AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017 u
                    A B R)
                  1)))) (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy021 A B R) from (by
          unfold nb089AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy024 u A B R)
        from (by
          unfold nb089AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014
                    A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy023 A B R), (nb089AlphaDummy026 u A B R)),
        ((nb089AlphaDummy022 A B R), (nb089AlphaDummy025 u A B R)),
        ((nb089AlphaDummy021 A B R), (nb089AlphaDummy024 u A B R)),
        ((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy013 A B R), (nb089AlphaDummy014 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠ (nb089AlphaDummy029 A B R)
        from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy023 A B R), (nb089AlphaDummy026 u A B R)),
        ((nb089AlphaDummy022 A B R), (nb089AlphaDummy025 u A B R)),
        ((nb089AlphaDummy021 A B R), (nb089AlphaDummy024 u A B R)),
        ((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy013 A B R), (nb089AlphaDummy014 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017
        u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠ (nb089AlphaDummy033 A B R)
        from (by
          unfold
            nb089AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy034 u A B R)
        from (by
          unfold
            nb089AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy022
        A B R) ≠ (nb089AlphaDummy033 A B R) from (by
          unfold
            nb089AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy034 u A B R)
        from (by
          unfold
            nb089AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠ (nb089AlphaDummy035 A B R)
        from (by
          unfold
            nb089AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy036 u A B R)
        from (by
          unfold
            nb089AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy035 A B R) from (by
          unfold
            nb089AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy036 u A B R)
        from (by
          unfold
            nb089AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy013 A B R), (nb089AlphaDummy014 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R) 0)))) (show (nb089AlphaDummy017 u A B R) ≠
        (nb089AlphaDummy020 u A B R) from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy013 A B R), (nb089AlphaDummy014 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show
                            (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy008 A B R) from
                            (by
                              unfold nb089AlphaDummy008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))))
                          (show u ≠ (nb089AlphaDummy010 u A B R) from (by
                              unfold nb089AlphaDummy010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0008 u A B R)
                                      1)))) (TAlphaVar.there (show
                              (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy007 A B R) from
                              (by
                                unfold nb089AlphaDummy007;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0006 A B R)
                                        0)))) (show u ≠ (nb089AlphaDummy009 u A B R) from (by
                                unfold nb089AlphaDummy009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0008 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy013 A B R)
                                from (by
                                  unfold nb089AlphaDummy013;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0010 A B R)
                                          0)))) (show u ≠ (nb089AlphaDummy014 u A B R) from
                                (by
                                  unfold nb089AlphaDummy014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0011 u A B R)
                                          0)))) (TAlphaVar.there (show
                                  (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy011 A B R)
                                  from (by
                                    unfold nb089AlphaDummy011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb089_support_mem_0007 A B R)
                                            0)))) (show u ≠ (nb089AlphaDummy012 u A B R) from
                                  (by
                                    unfold nb089AlphaDummy012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb089_support_mem_0009 u A B R) 0))))
                                (TAlphaVar.there (show (nb089AlphaDummy000 A B R) ≠
                                      (nb089AlphaDummy003 A B R) from (by
                                      unfold nb089AlphaDummy003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0004 A B R) 0))))
                                  (show u ≠ (nb089AlphaDummy004 u A B R) from (by
                                      unfold nb089AlphaDummy004;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0005 u A B R) 0))))
                                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb089AlphaDummy000 A B R))).fv ∪
                              ((Class.cv (nb089AlphaDummy003 A B R))).fv) (by decide))
                          (freshVar_injective (((Class.cv u)).fv ∪
                              ((Class.cv (nb089AlphaDummy004 u A B R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb089AlphaDummy008 A B R) ≠
                                      (nb089AlphaDummy015 A B R) from (by
                                      unfold nb089AlphaDummy015;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0012 A B R) 0)))) (show
                                    (nb089AlphaDummy010 u A B R) ≠
                                      (nb089AlphaDummy017 u A B R) from (by
                                      unfold nb089AlphaDummy017;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0013 u A B R) 0))))
                                  (TAlphaVar.there (show (nb089AlphaDummy008 A B R) ≠
                                        (nb089AlphaDummy016 A B R) from (by
                                        unfold nb089AlphaDummy016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0012 A B R) 1)))) (show
                                      (nb089AlphaDummy010 u A B R) ≠
                                        (nb089AlphaDummy018 u A B R) from (by
                                        unfold nb089AlphaDummy018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0013 u A B R) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb089AlphaDummy008 A B R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb089AlphaDummy010 u A B R))).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy022 A B R) from (by
          unfold nb089AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016 A
                    B R)
                  1)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy025 u A B R)
        from (by
          unfold nb089AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017 u
                    A B R)
                  1)))) (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy021 A B R) from (by
          unfold nb089AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0016
                    A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy024 u A B R)
        from (by
          unfold nb089AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0017
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014
                    A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy023 A B R), (nb089AlphaDummy026 u A B R)),
        ((nb089AlphaDummy022 A B R), (nb089AlphaDummy025 u A B R)),
        ((nb089AlphaDummy021 A B R), (nb089AlphaDummy024 u A B R)),
        ((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy013 A B R), (nb089AlphaDummy014 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠ (nb089AlphaDummy029 A B R)
        from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0021
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0018
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0019
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy029 A B R) from (by
          unfold
            nb089AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy030 u A B R)
        from (by
          unfold
            nb089AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0025
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy027 A B R) from (by
          unfold
            nb089AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy028 u A B R)
        from (by
          unfold
            nb089AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0023
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy023 A B R), (nb089AlphaDummy026 u A B R)),
        ((nb089AlphaDummy022 A B R), (nb089AlphaDummy025 u A B R)),
        ((nb089AlphaDummy021 A B R), (nb089AlphaDummy024 u A B R)),
        ((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy013 A B R), (nb089AlphaDummy014 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089AlphaDummy015 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017
        u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠ (nb089AlphaDummy033 A B R)
        from (by
          unfold
            nb089AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy034 u A B R)
        from (by
          unfold
            nb089AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy022
        A B R) ≠ (nb089AlphaDummy033 A B R) from (by
          unfold
            nb089AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy034 u A B R)
        from (by
          unfold
            nb089AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0029
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy022 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy025 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0027
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy015
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy017 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠ (nb089AlphaDummy035 A B R)
        from (by
          unfold
            nb089AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy036 u A B R)
        from (by
          unfold
            nb089AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy023
        A B R) ≠ (nb089AlphaDummy035 A B R) from (by
          unfold
            nb089AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy036 u A B R)
        from (by
          unfold
            nb089AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0033
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy023 A B R) ≠
        (nb089AlphaDummy031 A B R) from (by
          unfold
            nb089AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy026 u A B R) ≠ (nb089AlphaDummy032 u A B R)
        from (by
          unfold
            nb089AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0031
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy013 A B R), (nb089AlphaDummy014 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb089AlphaDummy015 A B R) ≠
        (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R) 0)))) (show (nb089AlphaDummy017 u A B R) ≠
        (nb089AlphaDummy020 u A B R) from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb089AlphaDummy015 A B R) ≠ (nb089AlphaDummy019 A B R) from (by
          unfold nb089AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0014 A B R)
                  0)))) (show (nb089AlphaDummy017 u A B R) ≠ (nb089AlphaDummy020 u A B R)
        from (by
          unfold nb089AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0015 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy019 A B R), (nb089AlphaDummy020 u A B R)),
        ((nb089AlphaDummy015 A B R), (nb089AlphaDummy017 u A B R)),
        ((nb089AlphaDummy016 A B R), (nb089AlphaDummy018 u A B R)),
        ((nb089AlphaDummy008 A B R), (nb089AlphaDummy010 u A B R)),
        ((nb089AlphaDummy007 A B R), (nb089AlphaDummy009 u A B R)),
        ((nb089AlphaDummy013 A B R), (nb089AlphaDummy014 u A B R)),
        ((nb089AlphaDummy011 A B R), (nb089AlphaDummy012 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb089SplitAlpha0000 u A B R)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb089SplitAlpha0000 u A B R)))))))))))

theorem nb089_focused_notmem_0000 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
            ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
          ((synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 (synCuni A))]
  rw [fv_syn_cpw1 (synCuni A)]
  rw [fv_syn_cuni A]
  exact hu

theorem nb089_wpp_notmem_0114 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv := by
  simpa only [nb089AlphaDummy003, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0000 A B R)

theorem nb089_focused_notmem_0001 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
          ((synCfdrowfib R A B (Class.cv u))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 (synCuni A))]
  rw [fv_syn_cpw1 (synCuni A)]
  rw [fv_syn_cuni A]
  exact hu

theorem nb089_wpp_notmem_0115 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv := by
  simpa only [nb089AlphaDummy004, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0001 u A B R)

theorem nb089_focused_notmem_0002 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb089_wpp_notmem_0116 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv := by
  simpa only [nb089AlphaDummy000, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0002 A B R)

theorem nb089_wpp_notmem_0117 (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    u ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv := by
  simpa only [fv_syn_cpw1, fv_syn_cuni] using dv_A_u

theorem nb089_focused_notmem_0003 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy005 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
            ({(nb089AlphaDummy003 A B R)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb089AlphaDummy000 A B R))
                (synCpw1 (synCpw1 (synCuni A))))
              (Wff.classEq (Class.cv (nb089AlphaDummy003 A B R))
                (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb089AlphaDummy000 A B R)) (synCpw1 (synCpw1 (synCuni A))))
      (Wff.classEq (Class.cv (nb089AlphaDummy003 A B R))
        (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb089AlphaDummy000 A B R))
      (synCpw1 (synCpw1 (synCuni A)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 (synCuni A))]
  rw [fv_syn_cpw1 (synCuni A)]
  rw [fv_syn_cuni A]
  exact hu

theorem nb089_wpp_notmem_0118 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy005 A B R) ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv := by
  simpa only [nb089AlphaDummy005, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0003 A B R)

theorem nb089_focused_notmem_0004 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy006 u A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb089AlphaDummy004 u A B R)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
              (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
                (synCfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
      (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
        (synCfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (synCpw1 (synCuni A))]
  rw [fv_syn_cpw1 (synCuni A)]
  rw [fv_syn_cuni A]
  exact hu

theorem nb089_wpp_notmem_0119 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy006 u A B R) ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv := by
  simpa only [nb089AlphaDummy006, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0004 u A B R)

theorem nb089_focused_notmem_0005 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy001 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((synWbr R (synCwe) A)).fv ∪
            ((synCmpt (nb089AlphaDummy000 A B R) (synCpw1 (synCpw1 (synCuni A)))
                (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))))).fv ∪
          ((synC0)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [fv_syn_wbr R (synCwe) A]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0120 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy001 A B R) ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv := by
  simpa only [nb089AlphaDummy001, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0005 A B R)

theorem nb089_focused_notmem_0006 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy002 u A B R) ∉ A.fv :=
  by
  change
    freshVar
        (((synWbr R (synCwe) A)).fv ∪ ((synCmpt u (synCpw1 (synCpw1 (synCuni A)))
                (synCfdrowfib R A B (Class.cv u)))).fv ∪ ((synC0)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [fv_syn_wbr R (synCwe) A]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0121 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy002 u A B R) ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv := by
  simpa only [nb089AlphaDummy002, fv_syn_cpw1, fv_syn_cuni] using
    (nb089_focused_notmem_0006 u A B R)

theorem nb089_compact_envfresh_0007 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) :
    TEnvFresh
      [((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u),
        ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
        ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      ((synCpw1 (synCpw1 (synCuni A)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb089AlphaDummy003 A B R) (nb089AlphaDummy004 u A B R)
      (nb089_wpp_notmem_0114 A B R) (nb089_wpp_notmem_0115 u A B R)
      (TEnvFresh.consFresh (nb089AlphaDummy000 A B R) u (nb089_wpp_notmem_0116 A B R)
        (nb089_wpp_notmem_0117 u A dv_A_u)
        (TEnvFresh.consFresh (nb089AlphaDummy005 A B R) (nb089AlphaDummy006 u A B R)
          (nb089_wpp_notmem_0118 A B R) (nb089_wpp_notmem_0119 u A B R)
          (TEnvFresh.consFresh (nb089AlphaDummy001 A B R)
            (nb089AlphaDummy002 u A B R) (nb089_wpp_notmem_0120 A B R)
            (nb089_wpp_notmem_0121 u A B R)
            (TEnvFresh.nil ((synCpw1 (synCpw1 (synCuni A)))).fv)))))

/-- Checked nominal proof certificate identified upstream as `nb089_wpp_refl_0007`. -/
@[expose]
noncomputable def nb089WppRefl0007 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) :
    TReflOn
      [((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u),
        ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
        ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      ((synCpw1 (synCpw1 (synCuni A)))).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0007 u A B R dv_A_u)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
