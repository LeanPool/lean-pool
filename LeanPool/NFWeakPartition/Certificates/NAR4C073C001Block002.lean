/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C073C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C073C001Part004`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb073_split_alpha_0000`. -/
@[expose]
noncomputable def nb073SplitAlpha0000 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb073AlphaDummy020), (nb073AlphaDummy021 x y)),
        ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
        ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
        ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy020))
          (Class.cab (nb073AlphaDummy014)
            (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
              (Wff.classEq (Class.cv (nb073AlphaDummy014))
                (synCphi (Class.cv (nb073AlphaDummy015))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy020)) (Class.cab (nb073AlphaDummy014)
              (synWrex (nb073AlphaDummy015) (Class.cv (nb073AlphaDummy000))
                (Wff.classEq (Class.cv (nb073AlphaDummy014))
                  (synCphi (Class.cv (nb073AlphaDummy015)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy021 x y))
          (Class.cab (nb073AlphaDummy016 x y)
            (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                (synCphi (Class.cv (nb073AlphaDummy017 x y))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy021 x y))
            (Class.cab (nb073AlphaDummy016 x y)
              (synWrex (nb073AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073AlphaDummy016 x y))
                  (synCphi (Class.cv (nb073AlphaDummy017 x y))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy015) from
                    (by
                      unfold nb073AlphaDummy015;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1))))
                  (show x ≠ (nb073AlphaDummy017 x y) from (by
                      unfold nb073AlphaDummy017;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb073_support_mem_0016 x y) 1)))) (TAlphaVar.there
                    (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy014) from (by
                        unfold nb073AlphaDummy014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 0))))
                    (show x ≠ (nb073AlphaDummy016 x y) from (by
                        unfold nb073AlphaDummy016;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb073_support_mem_0016 x y) 0))))
                    (TAlphaVar.there
                      (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy020) from (by
                          unfold nb073AlphaDummy020;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0018) 0))))
                      (show x ≠ (nb073AlphaDummy021 x y) from (by
                          unfold nb073AlphaDummy021;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0019 x y) 0))))
                      (TAlphaVar.there
                        (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy018) from (by
                            unfold nb073AlphaDummy018;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0015) 0))))
                        (show x ≠ (nb073AlphaDummy019 x y) from (by
                            unfold nb073AlphaDummy019;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0017 x y) 0))))
                        (TAlphaVar.there
                          (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy007) from (by
                              unfold nb073AlphaDummy007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0008) 1))))
                          (show x ≠ (nb073AlphaDummy009 x y) from (by
                              unfold nb073AlphaDummy009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0010 x y) 1))))
                          (TAlphaVar.there
                            (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy006) from (by
                                unfold nb073AlphaDummy006;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0008) 0))))
                            (show x ≠ (nb073AlphaDummy008 x y) from (by
                                unfold nb073AlphaDummy008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0010 x y) 0))))
                            (TAlphaVar.there
                              (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy012) from (by
                                  unfold nb073AlphaDummy012;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0012) 0))))
                              (show x ≠ (nb073AlphaDummy013 x y) from (by
                                  unfold nb073AlphaDummy013;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0013 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy010) from (by
                                    unfold nb073AlphaDummy010;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0009) 0))))
                                (show x ≠ (nb073AlphaDummy011 x y) from (by
                                    unfold nb073AlphaDummy011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0011 x y)
                                            0)))) (TAlphaVar.there
                                  (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy002) from
                                    (by
                                      unfold nb073AlphaDummy002;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0006)
                                              0)))) (show x ≠ (nb073AlphaDummy003 x y) from
                                    (by
                                      unfold nb073AlphaDummy003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0007 x y)
                                              0)))) (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_x_y (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb073AlphaDummy000))).fv ∪
                      ((Class.cv (nb073AlphaDummy001))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy022) from (by
                              unfold nb073AlphaDummy022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0020) 0))))
                          (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy024 x y) from
                            (by
                              unfold nb073AlphaDummy024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0021 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy023) from (by
                                unfold nb073AlphaDummy023;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0020) 1)))) (show
                              (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy025 x y) from (by
                                unfold nb073AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0021 x y) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073AlphaDummy015))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073AlphaDummy017 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy029) from (by
          unfold nb073AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 1)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy032 x y) from (by
          unfold nb073AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy022) ≠ (nb073AlphaDummy028) from (by
          unfold nb073AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 0)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy031 x y) from (by
          unfold nb073AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy026)
        from (by
          unfold nb073AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0022) 0)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy027 x y) from (by
          unfold nb073AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy030), (nb073AlphaDummy033 x y)), ((nb073AlphaDummy029),
        (nb073AlphaDummy032 x y)), ((nb073AlphaDummy028), (nb073AlphaDummy031 x y)),
        ((nb073AlphaDummy026), (nb073AlphaDummy027 x y)), ((nb073AlphaDummy022),
        (nb073AlphaDummy024 x y)), ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014),
        (nb073AlphaDummy016 x y)), ((nb073AlphaDummy020), (nb073AlphaDummy021 x y)),
        ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)), ((nb073AlphaDummy007),
        (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
        ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)), ((nb073AlphaDummy010),
        (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x), ((nb073AlphaDummy004),
        (nb073AlphaDummy005 x y))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy036) from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy036)
        from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy036) from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy036)
        from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy030), (nb073AlphaDummy033 x y)), ((nb073AlphaDummy029),
        (nb073AlphaDummy032 x y)), ((nb073AlphaDummy028), (nb073AlphaDummy031 x y)),
        ((nb073AlphaDummy026), (nb073AlphaDummy027 x y)), ((nb073AlphaDummy022),
        (nb073AlphaDummy024 x y)), ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014),
        (nb073AlphaDummy016 x y)), ((nb073AlphaDummy020), (nb073AlphaDummy021 x y)),
        ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)), ((nb073AlphaDummy007),
        (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
        ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)), ((nb073AlphaDummy010),
        (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x), ((nb073AlphaDummy004),
        (nb073AlphaDummy005 x y))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy022))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy024 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy040) from (by
          unfold
            nb073AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy041 x y) from (by
          unfold
            nb073AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy040)
        from (by
          unfold
            nb073AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy041 x y) from (by
          unfold
            nb073AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy042) from (by
          unfold
            nb073AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy043 x y) from (by
          unfold
            nb073AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠
        (nb073AlphaDummy042) from (by
          unfold
            nb073AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy043 x y) from (by
          unfold
            nb073AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from (by
                                        unfold nb073AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073AlphaDummy024 x y) ≠
                                        (nb073AlphaDummy027 x y) from (by
                                        unfold nb073AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy026), (nb073AlphaDummy027 x y)),
                                    ((nb073AlphaDummy022), (nb073AlphaDummy024 x y)),
                                    ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy020), (nb073AlphaDummy021 x y)),
                                    ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
                                    ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
                                    ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
                                    ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
                                    ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from
                                    (by
                                      unfold nb073AlphaDummy026;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0022)
                                              0)))) (show (nb073AlphaDummy024 x y) ≠
                                      (nb073AlphaDummy027 x y) from (by
                                      unfold nb073AlphaDummy027;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0023 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from (by
                                        unfold nb073AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073AlphaDummy024 x y) ≠
                                        (nb073AlphaDummy027 x y) from (by
                                        unfold nb073AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy026), (nb073AlphaDummy027 x y)),
                                    ((nb073AlphaDummy022), (nb073AlphaDummy024 x y)),
                                    ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy020), (nb073AlphaDummy021 x y)),
                                    ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
                                    ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
                                    ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
                                    ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
                                    ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy015) from
                      (by
                        unfold nb073AlphaDummy015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1))))
                    (show x ≠ (nb073AlphaDummy017 x y) from (by
                        unfold nb073AlphaDummy017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb073_support_mem_0016 x y) 1))))
                    (TAlphaVar.there
                      (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy014) from (by
                          unfold nb073AlphaDummy014;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0014) 0))))
                      (show x ≠ (nb073AlphaDummy016 x y) from (by
                          unfold nb073AlphaDummy016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0016 x y) 0))))
                      (TAlphaVar.there
                        (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy020) from (by
                            unfold nb073AlphaDummy020;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0018) 0))))
                        (show x ≠ (nb073AlphaDummy021 x y) from (by
                            unfold nb073AlphaDummy021;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0019 x y) 0))))
                        (TAlphaVar.there
                          (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy018) from (by
                              unfold nb073AlphaDummy018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0015) 0))))
                          (show x ≠ (nb073AlphaDummy019 x y) from (by
                              unfold nb073AlphaDummy019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0017 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy007) from (by
                                unfold nb073AlphaDummy007;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0008) 1))))
                            (show x ≠ (nb073AlphaDummy009 x y) from (by
                                unfold nb073AlphaDummy009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0010 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy006) from (by
                                  unfold nb073AlphaDummy006;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0008) 0))))
                              (show x ≠ (nb073AlphaDummy008 x y) from (by
                                  unfold nb073AlphaDummy008;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0010 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy012) from (by
                                    unfold nb073AlphaDummy012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0012) 0))))
                                (show x ≠ (nb073AlphaDummy013 x y) from (by
                                    unfold nb073AlphaDummy013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0013 x y)
                                            0)))) (TAlphaVar.there
                                  (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy010) from
                                    (by
                                      unfold nb073AlphaDummy010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0009)
                                              0)))) (show x ≠ (nb073AlphaDummy011 x y) from
                                    (by
                                      unfold nb073AlphaDummy011;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0011 x y)
                                              0)))) (TAlphaVar.there (show
                                      (nb073AlphaDummy000) ≠ (nb073AlphaDummy002) from (by
                                        unfold nb073AlphaDummy002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0006)
                                                0)))) (show x ≠ (nb073AlphaDummy003 x y) from
                                      (by
                                        unfold nb073AlphaDummy003;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0007 x y) 0))))
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide))
                                      dv_x_y (TAlphaVar.here _ _ _)))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb073AlphaDummy000))).fv ∪
                        ((Class.cv (nb073AlphaDummy001))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy022) from (by
                                unfold nb073AlphaDummy022;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0020) 0)))) (show
                              (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy024 x y) from (by
                                unfold nb073AlphaDummy024;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0021 x y) 0))))
                            (TAlphaVar.there
                              (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy023) from (by
                                  unfold nb073AlphaDummy023;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0020) 1)))) (show
                                (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy025 x y) from
                                (by
                                  unfold nb073AlphaDummy025;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0021 x y)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb073AlphaDummy015))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb073AlphaDummy017 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb073AlphaDummy022) ≠ (nb073AlphaDummy029) from (by
          unfold nb073AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 1)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy032 x y) from (by
          unfold nb073AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy028)
        from (by
          unfold nb073AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 0)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy031 x y) from (by
          unfold nb073AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy026)
        from (by
          unfold nb073AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0022)
                  0)))) (show (nb073AlphaDummy024 x y) ≠ (nb073AlphaDummy027 x y) from (by
          unfold nb073AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy030), (nb073AlphaDummy033 x y)), ((nb073AlphaDummy029),
        (nb073AlphaDummy032 x y)), ((nb073AlphaDummy028), (nb073AlphaDummy031 x y)),
        ((nb073AlphaDummy026), (nb073AlphaDummy027 x y)), ((nb073AlphaDummy022),
        (nb073AlphaDummy024 x y)), ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014),
        (nb073AlphaDummy016 x y)), ((nb073AlphaDummy020), (nb073AlphaDummy021 x y)),
        ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)), ((nb073AlphaDummy007),
        (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
        ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)), ((nb073AlphaDummy010),
        (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x), ((nb073AlphaDummy004),
        (nb073AlphaDummy005 x y))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy036) from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy036)
        from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy036) from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy036)
        from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy030), (nb073AlphaDummy033 x y)), ((nb073AlphaDummy029),
        (nb073AlphaDummy032 x y)), ((nb073AlphaDummy028), (nb073AlphaDummy031 x y)),
        ((nb073AlphaDummy026), (nb073AlphaDummy027 x y)), ((nb073AlphaDummy022),
        (nb073AlphaDummy024 x y)), ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014),
        (nb073AlphaDummy016 x y)), ((nb073AlphaDummy020), (nb073AlphaDummy021 x y)),
        ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)), ((nb073AlphaDummy007),
        (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
        ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)), ((nb073AlphaDummy010),
        (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x), ((nb073AlphaDummy004),
        (nb073AlphaDummy005 x y))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy022))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy024 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy040) from (by
          unfold
            nb073AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy041 x y) from (by
          unfold
            nb073AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy040)
        from (by
          unfold
            nb073AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy041 x y) from (by
          unfold
            nb073AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy042) from (by
          unfold
            nb073AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy043 x y) from (by
          unfold
            nb073AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠
        (nb073AlphaDummy042) from (by
          unfold
            nb073AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy043 x y) from (by
          unfold
            nb073AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from
                                        (by
                                          unfold nb073AlphaDummy026;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0022)
                                                  0)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy027 x y) from (by
                                          unfold nb073AlphaDummy027;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0023 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb073AlphaDummy026), (nb073AlphaDummy027 x y)),
                                      ((nb073AlphaDummy022), (nb073AlphaDummy024 x y)),
                                      ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
                                      ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                      ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                      ((nb073AlphaDummy020), (nb073AlphaDummy021 x y)),
                                      ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
                                      ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
                                      ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
                                      ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
                                      ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
                                      ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                      ((nb073AlphaDummy001), y),
                                      ((nb073AlphaDummy000), x), ((nb073AlphaDummy004),
                                        (nb073AlphaDummy005 x y))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from (by
                                        unfold nb073AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073AlphaDummy024 x y) ≠
                                        (nb073AlphaDummy027 x y) from (by
                                        unfold nb073AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from
                                        (by
                                          unfold nb073AlphaDummy026;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0022)
                                                  0)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy027 x y) from (by
                                          unfold nb073AlphaDummy027;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0023 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb073AlphaDummy026), (nb073AlphaDummy027 x y)),
                                      ((nb073AlphaDummy022), (nb073AlphaDummy024 x y)),
                                      ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
                                      ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                      ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                      ((nb073AlphaDummy020), (nb073AlphaDummy021 x y)),
                                      ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
                                      ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
                                      ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
                                      ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
                                      ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
                                      ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                      ((nb073AlphaDummy001), y),
                                      ((nb073AlphaDummy000), x), ((nb073AlphaDummy004),
                                        (nb073AlphaDummy005 x y))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C073C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb073_split_alpha_0001`. -/
@[expose]
noncomputable def nb073SplitAlpha0001 (x : Var) (y : Var) :
    TAlphaWff
      [((nb073AlphaDummy046), (nb073AlphaDummy047 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
        ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
        ((nb073AlphaDummy044), (nb073AlphaDummy045 x y)),
        ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
        ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
        ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy046))
          (synCcompl (synCphi (Class.cv (nb073AlphaDummy015))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy046)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy047 x y))
          (synCcompl (synCphi (Class.cv (nb073AlphaDummy017 x y))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy047 x y))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy022) from (by
                              unfold nb073AlphaDummy022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0020) 0))))
                          (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy024 x y) from
                            (by
                              unfold nb073AlphaDummy024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0021 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy023) from (by
                                unfold nb073AlphaDummy023;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0020) 1)))) (show
                              (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy025 x y) from (by
                                unfold nb073AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0021 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy048) from (by
                                  unfold nb073AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0058) 0)))) (show
                                (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy049 x y) from
                                (by
                                  unfold nb073AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0059 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy046) from (by
                                    unfold nb073AlphaDummy046;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0056) 0)))) (show
                                  (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy047 x y) from
                                  (by
                                    unfold nb073AlphaDummy047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0057 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073AlphaDummy015))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073AlphaDummy017 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy029) from (by
          unfold nb073AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 1)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy032 x y) from (by
          unfold nb073AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy022) ≠ (nb073AlphaDummy028) from (by
          unfold nb073AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 0)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy031 x y) from (by
          unfold nb073AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy026)
        from (by
          unfold nb073AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0022) 0)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy027 x y) from (by
          unfold nb073AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy030), (nb073AlphaDummy033 x y)), ((nb073AlphaDummy029),
        (nb073AlphaDummy032 x y)), ((nb073AlphaDummy028), (nb073AlphaDummy031 x y)),
        ((nb073AlphaDummy026), (nb073AlphaDummy027 x y)), ((nb073AlphaDummy022),
        (nb073AlphaDummy024 x y)), ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
        ((nb073AlphaDummy048), (nb073AlphaDummy049 x y)), ((nb073AlphaDummy046),
        (nb073AlphaDummy047 x y)), ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
        ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)), ((nb073AlphaDummy044),
        (nb073AlphaDummy045 x y)), ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006),
        (nb073AlphaDummy008 x y)), ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy036) from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy036)
        from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy036) from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy036)
        from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy030), (nb073AlphaDummy033 x y)), ((nb073AlphaDummy029),
        (nb073AlphaDummy032 x y)), ((nb073AlphaDummy028), (nb073AlphaDummy031 x y)),
        ((nb073AlphaDummy026), (nb073AlphaDummy027 x y)), ((nb073AlphaDummy022),
        (nb073AlphaDummy024 x y)), ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
        ((nb073AlphaDummy048), (nb073AlphaDummy049 x y)), ((nb073AlphaDummy046),
        (nb073AlphaDummy047 x y)), ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
        ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)), ((nb073AlphaDummy044),
        (nb073AlphaDummy045 x y)), ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006),
        (nb073AlphaDummy008 x y)), ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy022))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy024 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy029) ≠
        (nb073AlphaDummy040) from (by
          unfold
            nb073AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy041 x y) from (by
          unfold
            nb073AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy040)
        from (by
          unfold
            nb073AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy041 x y) from (by
          unfold
            nb073AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy042) from (by
          unfold
            nb073AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy043 x y) from (by
          unfold
            nb073AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠
        (nb073AlphaDummy042) from (by
          unfold
            nb073AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy043 x y) from (by
          unfold
            nb073AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from (by
                                        unfold nb073AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073AlphaDummy024 x y) ≠
                                        (nb073AlphaDummy027 x y) from (by
                                        unfold nb073AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy026), (nb073AlphaDummy027 x y)),
                                    ((nb073AlphaDummy022), (nb073AlphaDummy024 x y)),
                                    ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
                                    ((nb073AlphaDummy048), (nb073AlphaDummy049 x y)),
                                    ((nb073AlphaDummy046), (nb073AlphaDummy047 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy044), (nb073AlphaDummy045 x y)),
                                    ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
                                    ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
                                    ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
                                    ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
                                    ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from
                                    (by
                                      unfold nb073AlphaDummy026;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0022)
                                              0)))) (show (nb073AlphaDummy024 x y) ≠
                                      (nb073AlphaDummy027 x y) from (by
                                      unfold nb073AlphaDummy027;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0023 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from (by
                                        unfold nb073AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073AlphaDummy024 x y) ≠
                                        (nb073AlphaDummy027 x y) from (by
                                        unfold nb073AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy026), (nb073AlphaDummy027 x y)),
                                    ((nb073AlphaDummy022), (nb073AlphaDummy024 x y)),
                                    ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
                                    ((nb073AlphaDummy048), (nb073AlphaDummy049 x y)),
                                    ((nb073AlphaDummy046), (nb073AlphaDummy047 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy044), (nb073AlphaDummy045 x y)),
                                    ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
                                    ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
                                    ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
                                    ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
                                    ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy022) from (by
                              unfold nb073AlphaDummy022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0020) 0))))
                          (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy024 x y) from
                            (by
                              unfold nb073AlphaDummy024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0021 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy023) from (by
                                unfold nb073AlphaDummy023;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0020) 1)))) (show
                              (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy025 x y) from (by
                                unfold nb073AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0021 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy048) from (by
                                  unfold nb073AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0058) 0)))) (show
                                (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy049 x y) from
                                (by
                                  unfold nb073AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0059 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy046) from (by
                                    unfold nb073AlphaDummy046;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0056) 0)))) (show
                                  (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy047 x y) from
                                  (by
                                    unfold nb073AlphaDummy047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0057 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073AlphaDummy015))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073AlphaDummy017 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy029) from (by
          unfold nb073AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 1)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy032 x y) from (by
          unfold nb073AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy022) ≠ (nb073AlphaDummy028) from (by
          unfold nb073AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 0)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy031 x y) from (by
          unfold nb073AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy026)
        from (by
          unfold nb073AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0022) 0)))) (show (nb073AlphaDummy024 x y) ≠
        (nb073AlphaDummy027 x y) from (by
          unfold nb073AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy030), (nb073AlphaDummy033 x y)), ((nb073AlphaDummy029),
        (nb073AlphaDummy032 x y)), ((nb073AlphaDummy028), (nb073AlphaDummy031 x y)),
        ((nb073AlphaDummy026), (nb073AlphaDummy027 x y)), ((nb073AlphaDummy022),
        (nb073AlphaDummy024 x y)), ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
        ((nb073AlphaDummy048), (nb073AlphaDummy049 x y)), ((nb073AlphaDummy046),
        (nb073AlphaDummy047 x y)), ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
        ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)), ((nb073AlphaDummy044),
        (nb073AlphaDummy045 x y)), ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006),
        (nb073AlphaDummy008 x y)), ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy036) from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy036)
        from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy036) from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy036)
        from (by
          unfold
            nb073AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy037 x y) from (by
          unfold
            nb073AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy034)
        from (by
          unfold
            nb073AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy035 x y) from (by
          unfold
            nb073AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy030), (nb073AlphaDummy033 x y)), ((nb073AlphaDummy029),
        (nb073AlphaDummy032 x y)), ((nb073AlphaDummy028), (nb073AlphaDummy031 x y)),
        ((nb073AlphaDummy026), (nb073AlphaDummy027 x y)), ((nb073AlphaDummy022),
        (nb073AlphaDummy024 x y)), ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
        ((nb073AlphaDummy048), (nb073AlphaDummy049 x y)), ((nb073AlphaDummy046),
        (nb073AlphaDummy047 x y)), ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
        ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)), ((nb073AlphaDummy044),
        (nb073AlphaDummy045 x y)), ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006),
        (nb073AlphaDummy008 x y)), ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy022))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy024 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy029) ≠
        (nb073AlphaDummy040) from (by
          unfold
            nb073AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy041 x y) from (by
          unfold
            nb073AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy040)
        from (by
          unfold
            nb073AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy041 x y) from (by
          unfold
            nb073AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy029) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073AlphaDummy032 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy042) from (by
          unfold
            nb073AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy043 x y) from (by
          unfold
            nb073AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy030) ≠
        (nb073AlphaDummy042) from (by
          unfold
            nb073AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy043 x y) from (by
          unfold
            nb073AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy030) ≠ (nb073AlphaDummy038)
        from (by
          unfold
            nb073AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073AlphaDummy033 x y) ≠ (nb073AlphaDummy039 x y) from (by
          unfold
            nb073AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from (by
                                        unfold nb073AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073AlphaDummy024 x y) ≠
                                        (nb073AlphaDummy027 x y) from (by
                                        unfold nb073AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy026), (nb073AlphaDummy027 x y)),
                                    ((nb073AlphaDummy022), (nb073AlphaDummy024 x y)),
                                    ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
                                    ((nb073AlphaDummy048), (nb073AlphaDummy049 x y)),
                                    ((nb073AlphaDummy046), (nb073AlphaDummy047 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy044), (nb073AlphaDummy045 x y)),
                                    ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
                                    ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
                                    ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
                                    ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
                                    ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from
                                    (by
                                      unfold nb073AlphaDummy026;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0022)
                                              0)))) (show (nb073AlphaDummy024 x y) ≠
                                      (nb073AlphaDummy027 x y) from (by
                                      unfold nb073AlphaDummy027;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0023 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy022) ≠ (nb073AlphaDummy026) from (by
                                        unfold nb073AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073AlphaDummy024 x y) ≠
                                        (nb073AlphaDummy027 x y) from (by
                                        unfold nb073AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy026), (nb073AlphaDummy027 x y)),
                                    ((nb073AlphaDummy022), (nb073AlphaDummy024 x y)),
                                    ((nb073AlphaDummy023), (nb073AlphaDummy025 x y)),
                                    ((nb073AlphaDummy048), (nb073AlphaDummy049 x y)),
                                    ((nb073AlphaDummy046), (nb073AlphaDummy047 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy044), (nb073AlphaDummy045 x y)),
                                    ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
                                    ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
                                    ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
                                    ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
                                    ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb073AlphaDummy046), (nb073AlphaDummy047 x y)),
            ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
            ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
            ((nb073AlphaDummy044), (nb073AlphaDummy045 x y)),
            ((nb073AlphaDummy018), (nb073AlphaDummy019 x y)),
            ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
            ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
            ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
            ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
            ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
            ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
            ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
