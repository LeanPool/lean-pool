/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C094M3Part001

/-! NF weak partition development: NAR4H5C094M3Part002. -/


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

/-- Checked nominal proof certificate identified upstream as `nb094_split_alpha_0000`. -/
@[expose]
noncomputable def nb094SplitAlpha0000 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb094AlphaDummy020), (nb094AlphaDummy021 x y)),
        ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
        ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
        ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
        ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb094AlphaDummy020))
          (Class.cab (nb094AlphaDummy014)
            (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
              (Wff.classEq (Class.cv (nb094AlphaDummy014))
                (synCphi (Class.cv (nb094AlphaDummy015))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb094AlphaDummy020)) (Class.cab (nb094AlphaDummy014)
              (synWrex (nb094AlphaDummy015) (Class.cv (nb094AlphaDummy000))
                (Wff.classEq (Class.cv (nb094AlphaDummy014))
                  (synCphi (Class.cv (nb094AlphaDummy015)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb094AlphaDummy021 x y))
          (Class.cab (nb094AlphaDummy016 x y)
            (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                (synCphi (Class.cv (nb094AlphaDummy017 x y))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb094AlphaDummy021 x y))
            (Class.cab (nb094AlphaDummy016 x y)
              (synWrex (nb094AlphaDummy017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb094AlphaDummy016 x y))
                  (synCphi (Class.cv (nb094AlphaDummy017 x y))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy015) from
                    (by
                      unfold nb094AlphaDummy015;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0014) 1))))
                  (show x ≠ (nb094AlphaDummy017 x y) from (by
                      unfold nb094AlphaDummy017;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb094_support_mem_0016 x y) 1)))) (TAlphaVar.there
                    (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy014) from (by
                        unfold nb094AlphaDummy014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0014) 0))))
                    (show x ≠ (nb094AlphaDummy016 x y) from (by
                        unfold nb094AlphaDummy016;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb094_support_mem_0016 x y) 0))))
                    (TAlphaVar.there
                      (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy020) from (by
                          unfold nb094AlphaDummy020;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb094_support_mem_0018) 0))))
                      (show x ≠ (nb094AlphaDummy021 x y) from (by
                          unfold nb094AlphaDummy021;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb094_support_mem_0019 x y) 0))))
                      (TAlphaVar.there
                        (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy018) from (by
                            unfold nb094AlphaDummy018;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb094_support_mem_0015) 0))))
                        (show x ≠ (nb094AlphaDummy019 x y) from (by
                            unfold nb094AlphaDummy019;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb094_support_mem_0017 x y) 0))))
                        (TAlphaVar.there
                          (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy007) from (by
                              unfold nb094AlphaDummy007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0008) 1))))
                          (show x ≠ (nb094AlphaDummy009 x y) from (by
                              unfold nb094AlphaDummy009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0010 x y) 1))))
                          (TAlphaVar.there
                            (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy006) from (by
                                unfold nb094AlphaDummy006;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0008) 0))))
                            (show x ≠ (nb094AlphaDummy008 x y) from (by
                                unfold nb094AlphaDummy008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0010 x y) 0))))
                            (TAlphaVar.there
                              (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy012) from (by
                                  unfold nb094AlphaDummy012;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0012) 0))))
                              (show x ≠ (nb094AlphaDummy013 x y) from (by
                                  unfold nb094AlphaDummy013;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0013 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy010) from (by
                                    unfold nb094AlphaDummy010;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb094_support_mem_0009) 0))))
                                (show x ≠ (nb094AlphaDummy011 x y) from (by
                                    unfold nb094AlphaDummy011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb094_support_mem_0011 x y)
                                            0)))) (TAlphaVar.there
                                  (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy002) from
                                    (by
                                      unfold nb094AlphaDummy002;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0006)
                                              0)))) (show x ≠ (nb094AlphaDummy003 x y) from
                                    (by
                                      unfold nb094AlphaDummy003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0007 x y)
                                              0)))) (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_x_y (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb094AlphaDummy000))).fv ∪
                      ((Class.cv (nb094AlphaDummy001))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy022) from (by
                              unfold nb094AlphaDummy022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0020) 0))))
                          (show (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy024 x y) from
                            (by
                              unfold nb094AlphaDummy024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0021 x y) 0))))
                          (TAlphaVar.there
                            (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy023) from (by
                                unfold nb094AlphaDummy023;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0020) 1)))) (show
                              (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy025 x y) from (by
                                unfold nb094AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0021 x y) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb094AlphaDummy015))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb094AlphaDummy017 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy029) from (by
          unfold nb094AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0024) 1)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy032 x y) from (by
          unfold nb094AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0025 x y) 1)))) (TAlphaVar.there (show
        (nb094AlphaDummy022) ≠ (nb094AlphaDummy028) from (by
          unfold nb094AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0024) 0)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy031 x y) from (by
          unfold nb094AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy026)
        from (by
          unfold nb094AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0022) 0)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy027 x y) from (by
          unfold nb094AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy030), (nb094AlphaDummy033 x y)), ((nb094AlphaDummy029),
        (nb094AlphaDummy032 x y)), ((nb094AlphaDummy028), (nb094AlphaDummy031 x y)),
        ((nb094AlphaDummy026), (nb094AlphaDummy027 x y)), ((nb094AlphaDummy022),
        (nb094AlphaDummy024 x y)), ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
        ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)), ((nb094AlphaDummy014),
        (nb094AlphaDummy016 x y)), ((nb094AlphaDummy020), (nb094AlphaDummy021 x y)),
        ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)), ((nb094AlphaDummy007),
        (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
        ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)), ((nb094AlphaDummy010),
        (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
        ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x), ((nb094AlphaDummy004),
        (nb094AlphaDummy005 x y))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy036) from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0028)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0026)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy036)
        from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0032)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0030)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy036) from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0028)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0026)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy036)
        from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0032)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0030)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy030), (nb094AlphaDummy033 x y)), ((nb094AlphaDummy029),
        (nb094AlphaDummy032 x y)), ((nb094AlphaDummy028), (nb094AlphaDummy031 x y)),
        ((nb094AlphaDummy026), (nb094AlphaDummy027 x y)), ((nb094AlphaDummy022),
        (nb094AlphaDummy024 x y)), ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
        ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)), ((nb094AlphaDummy014),
        (nb094AlphaDummy016 x y)), ((nb094AlphaDummy020), (nb094AlphaDummy021 x y)),
        ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)), ((nb094AlphaDummy007),
        (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
        ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)), ((nb094AlphaDummy010),
        (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
        ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x), ((nb094AlphaDummy004),
        (nb094AlphaDummy005 x y))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy022))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy024 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy040) from (by
          unfold
            nb094AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0036)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy041 x y) from (by
          unfold
            nb094AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0034)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy040)
        from (by
          unfold
            nb094AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0036)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy041 x y) from (by
          unfold
            nb094AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0034)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy042) from (by
          unfold
            nb094AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0040)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy043 x y) from (by
          unfold
            nb094AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0038)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠
        (nb094AlphaDummy042) from (by
          unfold
            nb094AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0040)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy043 x y) from (by
          unfold
            nb094AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0038)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from (by
                                        unfold nb094AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0022)
                                                0)))) (show (nb094AlphaDummy024 x y) ≠
                                        (nb094AlphaDummy027 x y) from (by
                                        unfold nb094AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb094AlphaDummy026), (nb094AlphaDummy027 x y)),
                                    ((nb094AlphaDummy022), (nb094AlphaDummy024 x y)),
                                    ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
                                    ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
                                    ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
                                    ((nb094AlphaDummy020), (nb094AlphaDummy021 x y)),
                                    ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
                                    ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                    ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                    ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                    ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                    ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                    ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                                    ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from
                                    (by
                                      unfold nb094AlphaDummy026;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0022)
                                              0)))) (show (nb094AlphaDummy024 x y) ≠
                                      (nb094AlphaDummy027 x y) from (by
                                      unfold nb094AlphaDummy027;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0023 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from (by
                                        unfold nb094AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0022)
                                                0)))) (show (nb094AlphaDummy024 x y) ≠
                                        (nb094AlphaDummy027 x y) from (by
                                        unfold nb094AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb094AlphaDummy026), (nb094AlphaDummy027 x y)),
                                    ((nb094AlphaDummy022), (nb094AlphaDummy024 x y)),
                                    ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
                                    ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
                                    ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
                                    ((nb094AlphaDummy020), (nb094AlphaDummy021 x y)),
                                    ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
                                    ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                    ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                    ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                    ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                    ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                    ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                                    ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy015) from
                      (by
                        unfold nb094AlphaDummy015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0014) 1))))
                    (show x ≠ (nb094AlphaDummy017 x y) from (by
                        unfold nb094AlphaDummy017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb094_support_mem_0016 x y) 1))))
                    (TAlphaVar.there
                      (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy014) from (by
                          unfold nb094AlphaDummy014;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb094_support_mem_0014) 0))))
                      (show x ≠ (nb094AlphaDummy016 x y) from (by
                          unfold nb094AlphaDummy016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb094_support_mem_0016 x y) 0))))
                      (TAlphaVar.there
                        (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy020) from (by
                            unfold nb094AlphaDummy020;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb094_support_mem_0018) 0))))
                        (show x ≠ (nb094AlphaDummy021 x y) from (by
                            unfold nb094AlphaDummy021;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb094_support_mem_0019 x y) 0))))
                        (TAlphaVar.there
                          (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy018) from (by
                              unfold nb094AlphaDummy018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0015) 0))))
                          (show x ≠ (nb094AlphaDummy019 x y) from (by
                              unfold nb094AlphaDummy019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0017 x y) 0))))
                          (TAlphaVar.there
                            (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy007) from (by
                                unfold nb094AlphaDummy007;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0008) 1))))
                            (show x ≠ (nb094AlphaDummy009 x y) from (by
                                unfold nb094AlphaDummy009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0010 x y) 1))))
                            (TAlphaVar.there
                              (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy006) from (by
                                  unfold nb094AlphaDummy006;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0008) 0))))
                              (show x ≠ (nb094AlphaDummy008 x y) from (by
                                  unfold nb094AlphaDummy008;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0010 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy012) from (by
                                    unfold nb094AlphaDummy012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb094_support_mem_0012) 0))))
                                (show x ≠ (nb094AlphaDummy013 x y) from (by
                                    unfold nb094AlphaDummy013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb094_support_mem_0013 x y)
                                            0)))) (TAlphaVar.there
                                  (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy010) from
                                    (by
                                      unfold nb094AlphaDummy010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0009)
                                              0)))) (show x ≠ (nb094AlphaDummy011 x y) from
                                    (by
                                      unfold nb094AlphaDummy011;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0011 x y)
                                              0)))) (TAlphaVar.there (show
                                      (nb094AlphaDummy000) ≠ (nb094AlphaDummy002) from (by
                                        unfold nb094AlphaDummy002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0006)
                                                0)))) (show x ≠ (nb094AlphaDummy003 x y) from
                                      (by
                                        unfold nb094AlphaDummy003;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0007 x y) 0))))
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide))
                                      dv_x_y (TAlphaVar.here _ _ _)))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb094AlphaDummy000))).fv ∪
                        ((Class.cv (nb094AlphaDummy001))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy022) from (by
                                unfold nb094AlphaDummy022;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0020) 0)))) (show
                              (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy024 x y) from (by
                                unfold nb094AlphaDummy024;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0021 x y) 0))))
                            (TAlphaVar.there
                              (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy023) from (by
                                  unfold nb094AlphaDummy023;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0020) 1)))) (show
                                (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy025 x y) from
                                (by
                                  unfold nb094AlphaDummy025;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0021 x y)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb094AlphaDummy015))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb094AlphaDummy017 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb094AlphaDummy022) ≠ (nb094AlphaDummy029) from (by
          unfold nb094AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0024) 1)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy032 x y) from (by
          unfold nb094AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0025 x y)
                  1)))) (TAlphaVar.there (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy028)
        from (by
          unfold nb094AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0024) 0)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy031 x y) from (by
          unfold nb094AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy026)
        from (by
          unfold nb094AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0022)
                  0)))) (show (nb094AlphaDummy024 x y) ≠ (nb094AlphaDummy027 x y) from (by
          unfold nb094AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy030), (nb094AlphaDummy033 x y)), ((nb094AlphaDummy029),
        (nb094AlphaDummy032 x y)), ((nb094AlphaDummy028), (nb094AlphaDummy031 x y)),
        ((nb094AlphaDummy026), (nb094AlphaDummy027 x y)), ((nb094AlphaDummy022),
        (nb094AlphaDummy024 x y)), ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
        ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)), ((nb094AlphaDummy014),
        (nb094AlphaDummy016 x y)), ((nb094AlphaDummy020), (nb094AlphaDummy021 x y)),
        ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)), ((nb094AlphaDummy007),
        (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
        ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)), ((nb094AlphaDummy010),
        (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
        ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x), ((nb094AlphaDummy004),
        (nb094AlphaDummy005 x y))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy036) from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0028)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0026)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy036)
        from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0032)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0030)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy036) from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0028)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0026)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy036)
        from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0032)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0030)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy030), (nb094AlphaDummy033 x y)), ((nb094AlphaDummy029),
        (nb094AlphaDummy032 x y)), ((nb094AlphaDummy028), (nb094AlphaDummy031 x y)),
        ((nb094AlphaDummy026), (nb094AlphaDummy027 x y)), ((nb094AlphaDummy022),
        (nb094AlphaDummy024 x y)), ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
        ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)), ((nb094AlphaDummy014),
        (nb094AlphaDummy016 x y)), ((nb094AlphaDummy020), (nb094AlphaDummy021 x y)),
        ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)), ((nb094AlphaDummy007),
        (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
        ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)), ((nb094AlphaDummy010),
        (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
        ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x), ((nb094AlphaDummy004),
        (nb094AlphaDummy005 x y))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy022))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy024 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy040) from (by
          unfold
            nb094AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0036)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy041 x y) from (by
          unfold
            nb094AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0034)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy040)
        from (by
          unfold
            nb094AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0036)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy041 x y) from (by
          unfold
            nb094AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0034)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy042) from (by
          unfold
            nb094AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0040)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy043 x y) from (by
          unfold
            nb094AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0038)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠
        (nb094AlphaDummy042) from (by
          unfold
            nb094AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0040)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy043 x y) from (by
          unfold
            nb094AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0038)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from
                                        (by
                                          unfold nb094AlphaDummy026;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb094_support_mem_0022)
                                                  0)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy027 x y) from (by
                                          unfold nb094AlphaDummy027;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb094_support_mem_0023 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb094AlphaDummy026), (nb094AlphaDummy027 x y)),
                                      ((nb094AlphaDummy022), (nb094AlphaDummy024 x y)),
                                      ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
                                      ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
                                      ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
                                      ((nb094AlphaDummy020), (nb094AlphaDummy021 x y)),
                                      ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
                                      ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                      ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                      ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                      ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                      ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                      ((nb094AlphaDummy001), y),
                                      ((nb094AlphaDummy000), x), ((nb094AlphaDummy004),
                                        (nb094AlphaDummy005 x y))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from (by
                                        unfold nb094AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0022)
                                                0)))) (show (nb094AlphaDummy024 x y) ≠
                                        (nb094AlphaDummy027 x y) from (by
                                        unfold nb094AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from
                                        (by
                                          unfold nb094AlphaDummy026;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb094_support_mem_0022)
                                                  0)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy027 x y) from (by
                                          unfold nb094AlphaDummy027;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb094_support_mem_0023 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb094AlphaDummy026), (nb094AlphaDummy027 x y)),
                                      ((nb094AlphaDummy022), (nb094AlphaDummy024 x y)),
                                      ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
                                      ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
                                      ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
                                      ((nb094AlphaDummy020), (nb094AlphaDummy021 x y)),
                                      ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
                                      ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                      ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                      ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                      ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                      ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                      ((nb094AlphaDummy001), y),
                                      ((nb094AlphaDummy000), x), ((nb094AlphaDummy004),
                                        (nb094AlphaDummy005 x y))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb094_split_alpha_0001`. -/
@[expose]
noncomputable def nb094SplitAlpha0001 (x : Var) (y : Var) :
    TAlphaWff
      [((nb094AlphaDummy046), (nb094AlphaDummy047 x y)),
        ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
        ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
        ((nb094AlphaDummy044), (nb094AlphaDummy045 x y)),
        ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
        ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
        ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
        ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb094AlphaDummy046))
          (synCcompl (synCphi (Class.cv (nb094AlphaDummy015))))) (Wff.neg
          (Wff.classMem (Class.cv (nb094AlphaDummy046)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb094AlphaDummy047 x y))
          (synCcompl (synCphi (Class.cv (nb094AlphaDummy017 x y))))) (Wff.neg
          (Wff.classMem (Class.cv (nb094AlphaDummy047 x y))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy022) from (by
                              unfold nb094AlphaDummy022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0020) 0))))
                          (show (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy024 x y) from
                            (by
                              unfold nb094AlphaDummy024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0021 x y) 0))))
                          (TAlphaVar.there
                            (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy023) from (by
                                unfold nb094AlphaDummy023;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0020) 1)))) (show
                              (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy025 x y) from (by
                                unfold nb094AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0021 x y) 1))))
                            (TAlphaVar.there
                              (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy048) from (by
                                  unfold nb094AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0058) 0)))) (show
                                (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy049 x y) from
                                (by
                                  unfold nb094AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0059 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy046) from (by
                                    unfold nb094AlphaDummy046;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb094_support_mem_0056) 0)))) (show
                                  (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy047 x y) from
                                  (by
                                    unfold nb094AlphaDummy047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb094_support_mem_0057 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb094AlphaDummy015))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb094AlphaDummy017 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy029) from (by
          unfold nb094AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0024) 1)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy032 x y) from (by
          unfold nb094AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0025 x y) 1)))) (TAlphaVar.there (show
        (nb094AlphaDummy022) ≠ (nb094AlphaDummy028) from (by
          unfold nb094AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0024) 0)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy031 x y) from (by
          unfold nb094AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy026)
        from (by
          unfold nb094AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0022) 0)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy027 x y) from (by
          unfold nb094AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy030), (nb094AlphaDummy033 x y)), ((nb094AlphaDummy029),
        (nb094AlphaDummy032 x y)), ((nb094AlphaDummy028), (nb094AlphaDummy031 x y)),
        ((nb094AlphaDummy026), (nb094AlphaDummy027 x y)), ((nb094AlphaDummy022),
        (nb094AlphaDummy024 x y)), ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
        ((nb094AlphaDummy048), (nb094AlphaDummy049 x y)), ((nb094AlphaDummy046),
        (nb094AlphaDummy047 x y)), ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
        ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)), ((nb094AlphaDummy044),
        (nb094AlphaDummy045 x y)), ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006),
        (nb094AlphaDummy008 x y)), ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002),
        (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy036) from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0028)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0026)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy036)
        from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0032)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0030)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy036) from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0028)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0026)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy036)
        from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0032)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0030)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy030), (nb094AlphaDummy033 x y)), ((nb094AlphaDummy029),
        (nb094AlphaDummy032 x y)), ((nb094AlphaDummy028), (nb094AlphaDummy031 x y)),
        ((nb094AlphaDummy026), (nb094AlphaDummy027 x y)), ((nb094AlphaDummy022),
        (nb094AlphaDummy024 x y)), ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
        ((nb094AlphaDummy048), (nb094AlphaDummy049 x y)), ((nb094AlphaDummy046),
        (nb094AlphaDummy047 x y)), ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
        ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)), ((nb094AlphaDummy044),
        (nb094AlphaDummy045 x y)), ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006),
        (nb094AlphaDummy008 x y)), ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002),
        (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy022))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy024 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy029) ≠
        (nb094AlphaDummy040) from (by
          unfold
            nb094AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0036)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy041 x y) from (by
          unfold
            nb094AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0034)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy040)
        from (by
          unfold
            nb094AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0036)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy041 x y) from (by
          unfold
            nb094AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0034)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy042) from (by
          unfold
            nb094AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0040)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy043 x y) from (by
          unfold
            nb094AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0038)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠
        (nb094AlphaDummy042) from (by
          unfold
            nb094AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0040)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy043 x y) from (by
          unfold
            nb094AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0038)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from (by
                                        unfold nb094AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0022)
                                                0)))) (show (nb094AlphaDummy024 x y) ≠
                                        (nb094AlphaDummy027 x y) from (by
                                        unfold nb094AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb094AlphaDummy026), (nb094AlphaDummy027 x y)),
                                    ((nb094AlphaDummy022), (nb094AlphaDummy024 x y)),
                                    ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
                                    ((nb094AlphaDummy048), (nb094AlphaDummy049 x y)),
                                    ((nb094AlphaDummy046), (nb094AlphaDummy047 x y)),
                                    ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
                                    ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
                                    ((nb094AlphaDummy044), (nb094AlphaDummy045 x y)),
                                    ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
                                    ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                    ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                    ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                    ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                    ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                    ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                                    ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from
                                    (by
                                      unfold nb094AlphaDummy026;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0022)
                                              0)))) (show (nb094AlphaDummy024 x y) ≠
                                      (nb094AlphaDummy027 x y) from (by
                                      unfold nb094AlphaDummy027;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0023 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from (by
                                        unfold nb094AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0022)
                                                0)))) (show (nb094AlphaDummy024 x y) ≠
                                        (nb094AlphaDummy027 x y) from (by
                                        unfold nb094AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb094AlphaDummy026), (nb094AlphaDummy027 x y)),
                                    ((nb094AlphaDummy022), (nb094AlphaDummy024 x y)),
                                    ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
                                    ((nb094AlphaDummy048), (nb094AlphaDummy049 x y)),
                                    ((nb094AlphaDummy046), (nb094AlphaDummy047 x y)),
                                    ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
                                    ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
                                    ((nb094AlphaDummy044), (nb094AlphaDummy045 x y)),
                                    ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
                                    ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                    ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                    ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                    ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                    ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                    ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                                    ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy022) from (by
                              unfold nb094AlphaDummy022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0020) 0))))
                          (show (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy024 x y) from
                            (by
                              unfold nb094AlphaDummy024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0021 x y) 0))))
                          (TAlphaVar.there
                            (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy023) from (by
                                unfold nb094AlphaDummy023;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0020) 1)))) (show
                              (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy025 x y) from (by
                                unfold nb094AlphaDummy025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0021 x y) 1))))
                            (TAlphaVar.there
                              (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy048) from (by
                                  unfold nb094AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0058) 0)))) (show
                                (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy049 x y) from
                                (by
                                  unfold nb094AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0059 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb094AlphaDummy015) ≠ (nb094AlphaDummy046) from (by
                                    unfold nb094AlphaDummy046;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb094_support_mem_0056) 0)))) (show
                                  (nb094AlphaDummy017 x y) ≠ (nb094AlphaDummy047 x y) from
                                  (by
                                    unfold nb094AlphaDummy047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb094_support_mem_0057 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb094AlphaDummy015))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb094AlphaDummy017 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy029) from (by
          unfold nb094AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0024) 1)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy032 x y) from (by
          unfold nb094AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0025 x y) 1)))) (TAlphaVar.there (show
        (nb094AlphaDummy022) ≠ (nb094AlphaDummy028) from (by
          unfold nb094AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0024) 0)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy031 x y) from (by
          unfold nb094AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy026)
        from (by
          unfold nb094AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0022) 0)))) (show (nb094AlphaDummy024 x y) ≠
        (nb094AlphaDummy027 x y) from (by
          unfold nb094AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy030), (nb094AlphaDummy033 x y)), ((nb094AlphaDummy029),
        (nb094AlphaDummy032 x y)), ((nb094AlphaDummy028), (nb094AlphaDummy031 x y)),
        ((nb094AlphaDummy026), (nb094AlphaDummy027 x y)), ((nb094AlphaDummy022),
        (nb094AlphaDummy024 x y)), ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
        ((nb094AlphaDummy048), (nb094AlphaDummy049 x y)), ((nb094AlphaDummy046),
        (nb094AlphaDummy047 x y)), ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
        ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)), ((nb094AlphaDummy044),
        (nb094AlphaDummy045 x y)), ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006),
        (nb094AlphaDummy008 x y)), ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002),
        (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy036) from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0028)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0026)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy036)
        from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0032)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0030)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy036) from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0028)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0026)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy036)
        from (by
          unfold
            nb094AlphaDummy036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0032)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy037 x y) from (by
          unfold
            nb094AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy034)
        from (by
          unfold
            nb094AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0030)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy035 x y) from (by
          unfold
            nb094AlphaDummy035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy030), (nb094AlphaDummy033 x y)), ((nb094AlphaDummy029),
        (nb094AlphaDummy032 x y)), ((nb094AlphaDummy028), (nb094AlphaDummy031 x y)),
        ((nb094AlphaDummy026), (nb094AlphaDummy027 x y)), ((nb094AlphaDummy022),
        (nb094AlphaDummy024 x y)), ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
        ((nb094AlphaDummy048), (nb094AlphaDummy049 x y)), ((nb094AlphaDummy046),
        (nb094AlphaDummy047 x y)), ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
        ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)), ((nb094AlphaDummy044),
        (nb094AlphaDummy045 x y)), ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006),
        (nb094AlphaDummy008 x y)), ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002),
        (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy022))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy024 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy029) ≠
        (nb094AlphaDummy040) from (by
          unfold
            nb094AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0036)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy041 x y) from (by
          unfold
            nb094AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0034)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy040)
        from (by
          unfold
            nb094AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0036)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy041 x y) from (by
          unfold
            nb094AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy029) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0034)
                  0)))) (show (nb094AlphaDummy032 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy042) from (by
          unfold
            nb094AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0040)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy043 x y) from (by
          unfold
            nb094AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0038)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy030) ≠
        (nb094AlphaDummy042) from (by
          unfold
            nb094AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0040)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy043 x y) from (by
          unfold
            nb094AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy030) ≠ (nb094AlphaDummy038)
        from (by
          unfold
            nb094AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0038)
                  0)))) (show (nb094AlphaDummy033 x y) ≠ (nb094AlphaDummy039 x y) from (by
          unfold
            nb094AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from (by
                                        unfold nb094AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0022)
                                                0)))) (show (nb094AlphaDummy024 x y) ≠
                                        (nb094AlphaDummy027 x y) from (by
                                        unfold nb094AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb094AlphaDummy026), (nb094AlphaDummy027 x y)),
                                    ((nb094AlphaDummy022), (nb094AlphaDummy024 x y)),
                                    ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
                                    ((nb094AlphaDummy048), (nb094AlphaDummy049 x y)),
                                    ((nb094AlphaDummy046), (nb094AlphaDummy047 x y)),
                                    ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
                                    ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
                                    ((nb094AlphaDummy044), (nb094AlphaDummy045 x y)),
                                    ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
                                    ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                    ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                    ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                    ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                    ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                    ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                                    ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from
                                    (by
                                      unfold nb094AlphaDummy026;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0022)
                                              0)))) (show (nb094AlphaDummy024 x y) ≠
                                      (nb094AlphaDummy027 x y) from (by
                                      unfold nb094AlphaDummy027;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0023 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy022) ≠ (nb094AlphaDummy026) from (by
                                        unfold nb094AlphaDummy026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0022)
                                                0)))) (show (nb094AlphaDummy024 x y) ≠
                                        (nb094AlphaDummy027 x y) from (by
                                        unfold nb094AlphaDummy027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb094AlphaDummy026), (nb094AlphaDummy027 x y)),
                                    ((nb094AlphaDummy022), (nb094AlphaDummy024 x y)),
                                    ((nb094AlphaDummy023), (nb094AlphaDummy025 x y)),
                                    ((nb094AlphaDummy048), (nb094AlphaDummy049 x y)),
                                    ((nb094AlphaDummy046), (nb094AlphaDummy047 x y)),
                                    ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
                                    ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
                                    ((nb094AlphaDummy044), (nb094AlphaDummy045 x y)),
                                    ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
                                    ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                    ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                    ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                    ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                    ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                    ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                                    ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb094AlphaDummy046), (nb094AlphaDummy047 x y)),
            ((nb094AlphaDummy015), (nb094AlphaDummy017 x y)),
            ((nb094AlphaDummy014), (nb094AlphaDummy016 x y)),
            ((nb094AlphaDummy044), (nb094AlphaDummy045 x y)),
            ((nb094AlphaDummy018), (nb094AlphaDummy019 x y)),
            ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
            ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
            ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
            ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
            ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
            ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
            ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nb094_split_alpha_0002`. -/
@[expose]
noncomputable def nb094SplitAlpha0002 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
        ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
        ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb094AlphaDummy012))
          (Class.cab (nb094AlphaDummy006) (synWrex (nb094AlphaDummy007)
              (synCop (Class.cv (nb094AlphaDummy000)) (Class.cv (nb094AlphaDummy001)))
              (Wff.classEq (Class.cv (nb094AlphaDummy006))
                (synCphi (Class.cv (nb094AlphaDummy007))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb094AlphaDummy012)) (Class.cab (nb094AlphaDummy006)
              (synWrex (nb094AlphaDummy007) (synCop (Class.cv (nb094AlphaDummy000))
                  (Class.cv (nb094AlphaDummy001)))
                (Wff.classEq (Class.cv (nb094AlphaDummy006))
                  (synCphi (Class.cv (nb094AlphaDummy007)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb094AlphaDummy013 x y))
          (Class.cab (nb094AlphaDummy008 x y)
            (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                (synCphi (Class.cv (nb094AlphaDummy009 x y))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb094AlphaDummy013 x y))
            (Class.cab (nb094AlphaDummy008 x y)
              (synWrex (nb094AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
                  (synCphi (Class.cv (nb094AlphaDummy009 x y))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb094SplitAlpha0000 x y dv_x_y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb094AlphaDummy001) ≠
        (nb094AlphaDummy015) from (by
          unfold nb094AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0050) 1)))) (show y ≠ (nb094AlphaDummy017 x y) from (by
          unfold nb094AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0052 x y) 1)))) (TAlphaVar.there (show
        (nb094AlphaDummy001) ≠ (nb094AlphaDummy014) from (by
          unfold nb094AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0050) 0)))) (show y ≠ (nb094AlphaDummy016 x y) from (by
          unfold nb094AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0052 x y) 0)))) (TAlphaVar.there (show
        (nb094AlphaDummy001) ≠ (nb094AlphaDummy044) from (by
          unfold nb094AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0054) 0)))) (show y ≠ (nb094AlphaDummy045 x y) from (by
          unfold nb094AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0055 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy018)
        from (by
          unfold nb094AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0051) 0)))) (show y ≠ (nb094AlphaDummy019 x y) from (by
          unfold nb094AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0053 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy007)
        from (by
          unfold nb094AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0044)
                  1)))) (show y ≠ (nb094AlphaDummy009 x y) from (by
          unfold nb094AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0046 x y)
                  1)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy006)
        from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0044)
                  0)))) (show y ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0046 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy012)
        from (by
          unfold nb094AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0048)
                  0)))) (show y ≠ (nb094AlphaDummy013 x y) from (by
          unfold nb094AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0049
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy010)
        from (by
          unfold nb094AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0045)
                  0)))) (show y ≠ (nb094AlphaDummy011 x y) from (by
          unfold nb094AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0047
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy002)
        from (by
          unfold
            nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094AlphaDummy003 x y) from (by
          unfold
            nb094AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv)
        (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb094SplitAlpha0001 x y)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb094AlphaDummy001) ≠
        (nb094AlphaDummy015) from (by
          unfold nb094AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0050) 1)))) (show y ≠ (nb094AlphaDummy017 x y) from (by
          unfold nb094AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0052 x y) 1)))) (TAlphaVar.there (show
        (nb094AlphaDummy001) ≠ (nb094AlphaDummy014) from (by
          unfold nb094AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0050) 0)))) (show y ≠ (nb094AlphaDummy016 x y) from (by
          unfold nb094AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0052 x y) 0)))) (TAlphaVar.there (show
        (nb094AlphaDummy001) ≠ (nb094AlphaDummy044) from (by
          unfold nb094AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0054) 0)))) (show y ≠ (nb094AlphaDummy045 x y) from (by
          unfold nb094AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0055 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy018)
        from (by
          unfold nb094AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0051) 0)))) (show y ≠ (nb094AlphaDummy019 x y) from (by
          unfold nb094AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0053 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy007)
        from (by
          unfold nb094AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0044)
                  1)))) (show y ≠ (nb094AlphaDummy009 x y) from (by
          unfold nb094AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0046 x y)
                  1)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy006)
        from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0044)
                  0)))) (show y ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0046 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy012)
        from (by
          unfold nb094AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0048)
                  0)))) (show y ≠ (nb094AlphaDummy013 x y) from (by
          unfold nb094AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0049
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy010)
        from (by
          unfold nb094AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0045)
                  0)))) (show y ≠ (nb094AlphaDummy011 x y) from (by
          unfold nb094AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0047
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy002)
        from (by
          unfold
            nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094AlphaDummy003 x y) from (by
          unfold
            nb094AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb094AlphaDummy000))).fv ∪ ((Class.cv (nb094AlphaDummy001))).fv)
        (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb094SplitAlpha0001 x y))))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((synCop (Class.cv (nb094AlphaDummy000))
                          (Class.cv (nb094AlphaDummy001)))).fv ∪
                      ((Class.cv (nb094AlphaDummy002))).fv) (by decide)) (freshVar_injective
                    (((synCop (Class.cv x) (Class.cv y))).fv ∪
                      ((Class.cv (nb094AlphaDummy003 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb094AlphaDummy007) ≠ (nb094AlphaDummy050) from (by
                              unfold nb094AlphaDummy050;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0060) 0))))
                          (show (nb094AlphaDummy009 x y) ≠ (nb094AlphaDummy052 x y) from
                            (by
                              unfold nb094AlphaDummy052;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0061 x y) 0))))
                          (TAlphaVar.there
                            (show (nb094AlphaDummy007) ≠ (nb094AlphaDummy051) from (by
                                unfold nb094AlphaDummy051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0060) 1)))) (show
                              (nb094AlphaDummy009 x y) ≠ (nb094AlphaDummy053 x y) from (by
                                unfold nb094AlphaDummy053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0061 x y) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb094AlphaDummy007))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb094AlphaDummy009 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy057) from (by
          unfold nb094AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064) 1)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy060 x y) from (by
          unfold nb094AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065 x y) 1)))) (TAlphaVar.there (show
        (nb094AlphaDummy050) ≠ (nb094AlphaDummy056) from (by
          unfold nb094AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064) 0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy059 x y) from (by
          unfold nb094AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054)
        from (by
          unfold nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy055 x y) from (by
          unfold nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy058), (nb094AlphaDummy061 x y)), ((nb094AlphaDummy057),
        (nb094AlphaDummy060 x y)), ((nb094AlphaDummy056), (nb094AlphaDummy059 x y)),
        ((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006),
        (nb094AlphaDummy008 x y)), ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002),
        (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy064)
        from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy064)
        from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy058), (nb094AlphaDummy061 x y)), ((nb094AlphaDummy057),
        (nb094AlphaDummy060 x y)), ((nb094AlphaDummy056), (nb094AlphaDummy059 x y)),
        ((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006),
        (nb094AlphaDummy008 x y)), ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002),
        (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy050))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy057) ≠
        (nb094AlphaDummy068) from (by
          unfold
            nb094AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy069 x y) from (by
          unfold
            nb094AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy068)
        from (by
          unfold
            nb094AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy069 x y) from (by
          unfold
            nb094AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy070) from (by
          unfold
            nb094AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy071 x y) from (by
          unfold
            nb094AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠
        (nb094AlphaDummy070) from (by
          unfold
            nb094AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy071 x y) from (by
          unfold
            nb094AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from (by
                                        unfold nb094AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0062)
                                                0)))) (show (nb094AlphaDummy052 x y) ≠
                                        (nb094AlphaDummy055 x y) from (by
                                        unfold nb094AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0063 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb094AlphaDummy054), (nb094AlphaDummy055 x y)),
                                    ((nb094AlphaDummy050), (nb094AlphaDummy052 x y)),
                                    ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
                                    ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                    ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                    ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                    ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                    ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                    ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                                    ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from
                                    (by
                                      unfold nb094AlphaDummy054;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0062)
                                              0)))) (show (nb094AlphaDummy052 x y) ≠
                                      (nb094AlphaDummy055 x y) from (by
                                      unfold nb094AlphaDummy055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb094_support_mem_0063 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from (by
                                        unfold nb094AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0062)
                                                0)))) (show (nb094AlphaDummy052 x y) ≠
                                        (nb094AlphaDummy055 x y) from (by
                                        unfold nb094AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0063 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb094AlphaDummy054), (nb094AlphaDummy055 x y)),
                                    ((nb094AlphaDummy050), (nb094AlphaDummy052 x y)),
                                    ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
                                    ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                    ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                    ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                    ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                    ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                    ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                                    ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb094SplitAlpha0000 x y dv_x_y)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy015) from (by
          unfold nb094AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0050) 1)))) (show y ≠ (nb094AlphaDummy017 x y) from (by
          unfold nb094AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0052 x y) 1)))) (TAlphaVar.there (show
        (nb094AlphaDummy001) ≠ (nb094AlphaDummy014) from (by
          unfold nb094AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0050) 0)))) (show y ≠ (nb094AlphaDummy016 x y) from (by
          unfold nb094AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0052 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy044)
        from (by
          unfold nb094AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0054) 0)))) (show y ≠ (nb094AlphaDummy045 x y) from (by
          unfold nb094AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0055 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy018)
        from (by
          unfold nb094AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0051)
                  0)))) (show y ≠ (nb094AlphaDummy019 x y) from (by
          unfold nb094AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0053 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy007)
        from (by
          unfold nb094AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0044)
                  1)))) (show y ≠ (nb094AlphaDummy009 x y) from (by
          unfold nb094AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0046 x
                    y)
                  1)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy006)
        from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0044)
                  0)))) (show y ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0046
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy012)
        from (by
          unfold nb094AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0048)
                  0)))) (show y ≠ (nb094AlphaDummy013 x y) from (by
          unfold nb094AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0049
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy010)
        from (by
          unfold
            nb094AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0045)
                  0)))) (show y ≠ (nb094AlphaDummy011 x y) from (by
          unfold
            nb094AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0047
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy002)
        from (by
          unfold
            nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094AlphaDummy003 x y) from (by
          unfold
            nb094AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy000))).fv ∪
        ((Class.cv (nb094AlphaDummy001))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb094SplitAlpha0001 x y)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy015) from (by
          unfold nb094AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0050) 1)))) (show y ≠ (nb094AlphaDummy017 x y) from (by
          unfold nb094AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0052 x y) 1)))) (TAlphaVar.there (show
        (nb094AlphaDummy001) ≠ (nb094AlphaDummy014) from (by
          unfold nb094AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0050) 0)))) (show y ≠ (nb094AlphaDummy016 x y) from (by
          unfold nb094AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0052 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy044)
        from (by
          unfold nb094AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0054) 0)))) (show y ≠ (nb094AlphaDummy045 x y) from (by
          unfold nb094AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0055 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy018)
        from (by
          unfold nb094AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0051)
                  0)))) (show y ≠ (nb094AlphaDummy019 x y) from (by
          unfold nb094AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0053 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy007)
        from (by
          unfold nb094AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0044)
                  1)))) (show y ≠ (nb094AlphaDummy009 x y) from (by
          unfold nb094AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0046 x
                    y)
                  1)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy006)
        from (by
          unfold nb094AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0044)
                  0)))) (show y ≠ (nb094AlphaDummy008 x y) from (by
          unfold nb094AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0046
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy012)
        from (by
          unfold nb094AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0048)
                  0)))) (show y ≠ (nb094AlphaDummy013 x y) from (by
          unfold nb094AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0049
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy010)
        from (by
          unfold
            nb094AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0045)
                  0)))) (show y ≠ (nb094AlphaDummy011 x y) from (by
          unfold
            nb094AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0047
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy002)
        from (by
          unfold
            nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094AlphaDummy003 x y) from (by
          unfold
            nb094AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy000))).fv ∪
        ((Class.cv (nb094AlphaDummy001))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb094SplitAlpha0001 x y))))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((synCop (Class.cv (nb094AlphaDummy000))
                            (Class.cv (nb094AlphaDummy001)))).fv ∪
                        ((Class.cv (nb094AlphaDummy002))).fv) (by decide))
                    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
                        ((Class.cv (nb094AlphaDummy003 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb094AlphaDummy007) ≠ (nb094AlphaDummy050) from (by
                                unfold nb094AlphaDummy050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0060) 0)))) (show
                              (nb094AlphaDummy009 x y) ≠ (nb094AlphaDummy052 x y) from (by
                                unfold nb094AlphaDummy052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0061 x y) 0))))
                            (TAlphaVar.there
                              (show (nb094AlphaDummy007) ≠ (nb094AlphaDummy051) from (by
                                  unfold nb094AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0060) 1)))) (show
                                (nb094AlphaDummy009 x y) ≠ (nb094AlphaDummy053 x y) from
                                (by
                                  unfold nb094AlphaDummy053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb094_support_mem_0061 x y)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb094AlphaDummy007))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb094AlphaDummy009 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb094AlphaDummy050) ≠ (nb094AlphaDummy057) from (by
          unfold nb094AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064) 1)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy060 x y) from (by
          unfold nb094AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065 x y)
                  1)))) (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy056)
        from (by
          unfold nb094AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064) 0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy059 x y) from (by
          unfold nb094AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054)
        from (by
          unfold nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062)
                  0)))) (show (nb094AlphaDummy052 x y) ≠ (nb094AlphaDummy055 x y) from (by
          unfold nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy058), (nb094AlphaDummy061 x y)), ((nb094AlphaDummy057),
        (nb094AlphaDummy060 x y)), ((nb094AlphaDummy056), (nb094AlphaDummy059 x y)),
        ((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006),
        (nb094AlphaDummy008 x y)), ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002),
        (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy064)
        from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy064)
        from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy058), (nb094AlphaDummy061 x y)), ((nb094AlphaDummy057),
        (nb094AlphaDummy060 x y)), ((nb094AlphaDummy056), (nb094AlphaDummy059 x y)),
        ((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)), ((nb094AlphaDummy006),
        (nb094AlphaDummy008 x y)), ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)), ((nb094AlphaDummy002),
        (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy050))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy057) ≠
        (nb094AlphaDummy068) from (by
          unfold
            nb094AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy069 x y) from (by
          unfold
            nb094AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy068)
        from (by
          unfold
            nb094AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy069 x y) from (by
          unfold
            nb094AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy070) from (by
          unfold
            nb094AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy071 x y) from (by
          unfold
            nb094AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠
        (nb094AlphaDummy070) from (by
          unfold
            nb094AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy071 x y) from (by
          unfold
            nb094AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from
                                        (by
                                          unfold nb094AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb094_support_mem_0062)
                                                  0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy055 x y) from (by
                                          unfold nb094AlphaDummy055;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb094_support_mem_0063 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb094AlphaDummy054), (nb094AlphaDummy055 x y)),
                                      ((nb094AlphaDummy050), (nb094AlphaDummy052 x y)),
                                      ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
                                      ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                      ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                      ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                      ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                      ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                      ((nb094AlphaDummy001), y),
                                      ((nb094AlphaDummy000), x), ((nb094AlphaDummy004),
                                        (nb094AlphaDummy005 x y))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from (by
                                        unfold nb094AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0062)
                                                0)))) (show (nb094AlphaDummy052 x y) ≠
                                        (nb094AlphaDummy055 x y) from (by
                                        unfold nb094AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0063 x y) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from
                                        (by
                                          unfold nb094AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb094_support_mem_0062)
                                                  0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy055 x y) from (by
                                          unfold nb094AlphaDummy055;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb094_support_mem_0063 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb094AlphaDummy054), (nb094AlphaDummy055 x y)),
                                      ((nb094AlphaDummy050), (nb094AlphaDummy052 x y)),
                                      ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
                                      ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                                      ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                                      ((nb094AlphaDummy012), (nb094AlphaDummy013 x y)),
                                      ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                                      ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                                      ((nb094AlphaDummy001), y),
                                      ((nb094AlphaDummy000), x), ((nb094AlphaDummy004),
                                        (nb094AlphaDummy005 x y))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
