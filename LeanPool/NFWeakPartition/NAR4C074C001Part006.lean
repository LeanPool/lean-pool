/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C074C001Part005

/-! NF weak partition development: NAR4C074C001Part006. -/


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

/-- Checked nominal proof certificate identified upstream as `nb074_split_alpha_0001`. -/
@[expose]
noncomputable def nb074SplitAlpha0001 (x : Var) :
    TAlphaWff
      [((nb074AlphaDummy035), (nb074AlphaDummy036 x)),
        ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy035))
          (Class.cab (nb074AlphaDummy005)
            (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
              (Wff.classEq (Class.cv (nb074AlphaDummy005))
                (synCun (synCphi (Class.cv (nb074AlphaDummy006))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb074AlphaDummy035))
            (Class.cab (nb074AlphaDummy005)
              (synWrex (nb074AlphaDummy006) (Class.cv (nb074AlphaDummy001))
                (Wff.classEq (Class.cv (nb074AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy006)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy036 x))
          (Class.cab (nb074AlphaDummy007 x)
            (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy036 x))
            (Class.cab (nb074AlphaDummy007 x)
              (synWrex (nb074AlphaDummy008 x) (Class.cv (nb074AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb074AlphaDummy008 x)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb074AlphaDummy001) ≠ (nb074AlphaDummy006) from
                    (by
                      unfold nb074AlphaDummy006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 1))))
                  (show (nb074AlphaDummy002 x) ≠ (nb074AlphaDummy008 x) from (by
                      unfold nb074AlphaDummy008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 1))))
                  (TAlphaVar.there (show (nb074AlphaDummy001) ≠ (nb074AlphaDummy005) from
                      (by
                        unfold nb074AlphaDummy005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 0))))
                    (show (nb074AlphaDummy002 x) ≠ (nb074AlphaDummy007 x) from (by
                        unfold nb074AlphaDummy007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0036 x) 0)))) (TAlphaVar.there
                      (show (nb074AlphaDummy001) ≠ (nb074AlphaDummy035) from (by
                          unfold nb074AlphaDummy035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0038) 0))))
                      (show (nb074AlphaDummy002 x) ≠ (nb074AlphaDummy036 x) from (by
                          unfold nb074AlphaDummy036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0039 x) 0))))
                      (TAlphaVar.there
                        (show (nb074AlphaDummy001) ≠ (nb074AlphaDummy009) from (by
                            unfold nb074AlphaDummy009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0035) 0))))
                        (show (nb074AlphaDummy002 x) ≠ (nb074AlphaDummy010 x) from (by
                            unfold nb074AlphaDummy010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0037 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy000))).fv ∪
                      ((Class.cv (nb074AlphaDummy001))).fv) (by decide)) (freshVar_injective
                    (((Class.cv x)).fv ∪ ((Class.cv (nb074AlphaDummy002 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb074AlphaDummy006) ≠
        (nb074AlphaDummy013) from (by
          unfold nb074AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 0)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy015 x) from (by
          unfold nb074AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy006) ≠ (nb074AlphaDummy014) from (by
          unfold nb074AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 1)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy016 x) from (by
          unfold nb074AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy006) ≠ (nb074AlphaDummy039) from (by
          unfold nb074AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0042) 0)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy040 x) from (by
          unfold nb074AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0043 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy006) ≠ (nb074AlphaDummy037) from (by
          unfold nb074AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0040) 0)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy038 x) from (by
          unfold nb074AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0041 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb074AlphaDummy006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠
        (nb074AlphaDummy020) from (by
          unfold
            nb074AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  1)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy023 x) from (by
          unfold
            nb074AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy019)
        from (by
          unfold
            nb074AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy022 x) from (by
          unfold
            nb074AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold
            nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold
            nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy021), (nb074AlphaDummy024 x)), ((nb074AlphaDummy020),
        (nb074AlphaDummy023 x)), ((nb074AlphaDummy019), (nb074AlphaDummy022 x)),
        ((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy039), (nb074AlphaDummy040 x)), ((nb074AlphaDummy037),
        (nb074AlphaDummy038 x)), ((nb074AlphaDummy006), (nb074AlphaDummy008 x)),
        ((nb074AlphaDummy005), (nb074AlphaDummy007 x)), ((nb074AlphaDummy035),
        (nb074AlphaDummy036 x)), ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy020) ≠ (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy021), (nb074AlphaDummy024 x)), ((nb074AlphaDummy020),
        (nb074AlphaDummy023 x)), ((nb074AlphaDummy019), (nb074AlphaDummy022 x)),
        ((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy039), (nb074AlphaDummy040 x)), ((nb074AlphaDummy037),
        (nb074AlphaDummy038 x)), ((nb074AlphaDummy006), (nb074AlphaDummy008 x)),
        ((nb074AlphaDummy005), (nb074AlphaDummy007 x)), ((nb074AlphaDummy035),
        (nb074AlphaDummy036 x)), ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy020) ≠
        (nb074AlphaDummy031) from (by
          unfold
            nb074AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy032 x) from (by
          unfold
            nb074AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy020) ≠
        (nb074AlphaDummy031) from (by
          unfold
            nb074AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy032 x) from (by
          unfold
            nb074AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy033) from (by
          unfold
            nb074AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy034 x) from (by
          unfold
            nb074AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy033) from (by
          unfold
            nb074AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy034 x) from (by
          unfold
            nb074AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy039), (nb074AlphaDummy040 x)), ((nb074AlphaDummy037),
        (nb074AlphaDummy038 x)), ((nb074AlphaDummy006), (nb074AlphaDummy008 x)),
        ((nb074AlphaDummy005), (nb074AlphaDummy007 x)), ((nb074AlphaDummy035),
        (nb074AlphaDummy036 x)), ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy013) ≠ (nb074AlphaDummy017) from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy039), (nb074AlphaDummy040 x)), ((nb074AlphaDummy037),
        (nb074AlphaDummy038 x)), ((nb074AlphaDummy006), (nb074AlphaDummy008 x)),
        ((nb074AlphaDummy005), (nb074AlphaDummy007 x)), ((nb074AlphaDummy035),
        (nb074AlphaDummy036 x)), ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb074AlphaDummy006) ≠
        (nb074AlphaDummy013) from (by
          unfold nb074AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 0)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy015 x) from (by
          unfold nb074AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy006) ≠ (nb074AlphaDummy014) from (by
          unfold nb074AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 1)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy016 x) from (by
          unfold nb074AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy006) ≠ (nb074AlphaDummy039) from (by
          unfold nb074AlphaDummy039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0042) 0)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy040 x) from (by
          unfold nb074AlphaDummy040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0043 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy006) ≠ (nb074AlphaDummy037) from (by
          unfold nb074AlphaDummy037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0040) 0)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy038 x) from (by
          unfold nb074AlphaDummy038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0041 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb074AlphaDummy006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠
        (nb074AlphaDummy020) from (by
          unfold
            nb074AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  1)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy023 x) from (by
          unfold
            nb074AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy019)
        from (by
          unfold
            nb074AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy022 x) from (by
          unfold
            nb074AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold
            nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold
            nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy021), (nb074AlphaDummy024 x)), ((nb074AlphaDummy020),
        (nb074AlphaDummy023 x)), ((nb074AlphaDummy019), (nb074AlphaDummy022 x)),
        ((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy039), (nb074AlphaDummy040 x)), ((nb074AlphaDummy037),
        (nb074AlphaDummy038 x)), ((nb074AlphaDummy006), (nb074AlphaDummy008 x)),
        ((nb074AlphaDummy005), (nb074AlphaDummy007 x)), ((nb074AlphaDummy035),
        (nb074AlphaDummy036 x)), ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy020) ≠ (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy021), (nb074AlphaDummy024 x)), ((nb074AlphaDummy020),
        (nb074AlphaDummy023 x)), ((nb074AlphaDummy019), (nb074AlphaDummy022 x)),
        ((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy039), (nb074AlphaDummy040 x)), ((nb074AlphaDummy037),
        (nb074AlphaDummy038 x)), ((nb074AlphaDummy006), (nb074AlphaDummy008 x)),
        ((nb074AlphaDummy005), (nb074AlphaDummy007 x)), ((nb074AlphaDummy035),
        (nb074AlphaDummy036 x)), ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy020) ≠
        (nb074AlphaDummy031) from (by
          unfold
            nb074AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy032 x) from (by
          unfold
            nb074AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy020) ≠
        (nb074AlphaDummy031) from (by
          unfold
            nb074AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy032 x) from (by
          unfold
            nb074AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy033) from (by
          unfold
            nb074AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy034 x) from (by
          unfold
            nb074AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy033) from (by
          unfold
            nb074AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy034 x) from (by
          unfold
            nb074AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy039), (nb074AlphaDummy040 x)), ((nb074AlphaDummy037),
        (nb074AlphaDummy038 x)), ((nb074AlphaDummy006), (nb074AlphaDummy008 x)),
        ((nb074AlphaDummy005), (nb074AlphaDummy007 x)), ((nb074AlphaDummy035),
        (nb074AlphaDummy036 x)), ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy013) ≠ (nb074AlphaDummy017) from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy039), (nb074AlphaDummy040 x)), ((nb074AlphaDummy037),
        (nb074AlphaDummy038 x)), ((nb074AlphaDummy006), (nb074AlphaDummy008 x)),
        ((nb074AlphaDummy005), (nb074AlphaDummy007 x)), ((nb074AlphaDummy035),
        (nb074AlphaDummy036 x)), ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb074AlphaDummy037), (nb074AlphaDummy038 x)),
                          ((nb074AlphaDummy006), (nb074AlphaDummy008 x)),
                          ((nb074AlphaDummy005), (nb074AlphaDummy007 x)),
                          ((nb074AlphaDummy035), (nb074AlphaDummy036 x)),
                          ((nb074AlphaDummy009), (nb074AlphaDummy010 x)),
                          ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                          ((nb074AlphaDummy000), x),
                          ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb074SplitAlpha0000 x))

/-- Checked nominal proof certificate identified upstream as `nb074_split_alpha_0002`. -/
@[expose]
noncomputable def nb074SplitAlpha0002 (x : Var) :
    TAlphaWff
      [((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
      (Wff.classEq (Class.cv (nb074AlphaDummy003))
        (synCop (Class.cv (nb074AlphaDummy000)) (Class.cv (nb074AlphaDummy001))))
      (Wff.classEq (Class.cv (nb074AlphaDummy004 x))
        (synCop (Class.cv x) (Class.cv (nb074AlphaDummy002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb074AlphaDummy001) ≠ (nb074AlphaDummy003) from (by
              unfold nb074AlphaDummy003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0002) 0))))) (Ne.symm
          (show (nb074AlphaDummy002 x) ≠ (nb074AlphaDummy004 x) from (by
              unfold nb074AlphaDummy004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0003 x) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy003) from
              (by
                unfold nb074AlphaDummy003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0000) 0))))) (Ne.symm
            (show x ≠ (nb074AlphaDummy004 x) from (by
                unfold nb074AlphaDummy004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0001 x) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy006) from (by
                                    unfold nb074AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0006) 1))))
                                (show x ≠ (nb074AlphaDummy008 x) from (by
                                    unfold nb074AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0008 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy005) from
                                    (by
                                      unfold nb074AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0006)
                                              0)))) (show x ≠ (nb074AlphaDummy007 x) from (by
                                      unfold nb074AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0008 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb074AlphaDummy000) ≠ (nb074AlphaDummy011) from (by
                                        unfold nb074AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0010)
                                                0)))) (show x ≠ (nb074AlphaDummy012 x) from
                                      (by
                                        unfold nb074AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0011 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb074AlphaDummy000) ≠ (nb074AlphaDummy009) from
                                        (by
                                          unfold nb074AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0007)
                                                  0)))) (show x ≠ (nb074AlphaDummy010 x) from
                                        (by
                                          unfold nb074AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0009 x) 0))))
                                      (TAlphaVar.there (show (nb074AlphaDummy000) ≠
        (nb074AlphaDummy001) from (by
          unfold nb074AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0004) 0)))) (show x ≠ (nb074AlphaDummy002 x) from (by
          unfold nb074AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0005 x) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective (((Class.cv (nb074AlphaDummy000))).fv ∪
                                    ((Class.cv (nb074AlphaDummy001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb074AlphaDummy002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb074AlphaDummy006) ≠
        (nb074AlphaDummy013) from (by
          unfold nb074AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 0)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy015 x) from (by
          unfold nb074AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy006) ≠ (nb074AlphaDummy014) from (by
          unfold nb074AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 1)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy016 x) from (by
          unfold nb074AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb074AlphaDummy006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠
        (nb074AlphaDummy020) from (by
          unfold
            nb074AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  1)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy023 x) from (by
          unfold
            nb074AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy019)
        from (by
          unfold
            nb074AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy022 x) from (by
          unfold
            nb074AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold
            nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold
            nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy021), (nb074AlphaDummy024 x)), ((nb074AlphaDummy020),
        (nb074AlphaDummy023 x)), ((nb074AlphaDummy019), (nb074AlphaDummy022 x)),
        ((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy006), (nb074AlphaDummy008 x)), ((nb074AlphaDummy005),
        (nb074AlphaDummy007 x)), ((nb074AlphaDummy011), (nb074AlphaDummy012 x)),
        ((nb074AlphaDummy009), (nb074AlphaDummy010 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy021), (nb074AlphaDummy024 x)), ((nb074AlphaDummy020),
        (nb074AlphaDummy023 x)), ((nb074AlphaDummy019), (nb074AlphaDummy022 x)),
        ((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy006), (nb074AlphaDummy008 x)), ((nb074AlphaDummy005),
        (nb074AlphaDummy007 x)), ((nb074AlphaDummy011), (nb074AlphaDummy012 x)),
        ((nb074AlphaDummy009), (nb074AlphaDummy010 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy013))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy020) ≠
        (nb074AlphaDummy031) from (by
          unfold
            nb074AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy032 x) from (by
          unfold
            nb074AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy020) ≠
        (nb074AlphaDummy031) from (by
          unfold
            nb074AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy032 x) from (by
          unfold
            nb074AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy033) from (by
          unfold
            nb074AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy034 x) from (by
          unfold
            nb074AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy033) from (by
          unfold
            nb074AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy034 x) from (by
          unfold
            nb074AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy006), (nb074AlphaDummy008 x)), ((nb074AlphaDummy005),
        (nb074AlphaDummy007 x)), ((nb074AlphaDummy011), (nb074AlphaDummy012 x)),
        ((nb074AlphaDummy009), (nb074AlphaDummy010 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017) from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014) 0)))) (show (nb074AlphaDummy015 x) ≠
        (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy006), (nb074AlphaDummy008 x)), ((nb074AlphaDummy005),
        (nb074AlphaDummy007 x)), ((nb074AlphaDummy011), (nb074AlphaDummy012 x)),
        ((nb074AlphaDummy009), (nb074AlphaDummy010 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy006) from (by
                                    unfold nb074AlphaDummy006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0006) 1))))
                                (show x ≠ (nb074AlphaDummy008 x) from (by
                                    unfold nb074AlphaDummy008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0008 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy005) from
                                    (by
                                      unfold nb074AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0006)
                                              0)))) (show x ≠ (nb074AlphaDummy007 x) from (by
                                      unfold nb074AlphaDummy007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0008 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb074AlphaDummy000) ≠ (nb074AlphaDummy011) from (by
                                        unfold nb074AlphaDummy011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0010)
                                                0)))) (show x ≠ (nb074AlphaDummy012 x) from
                                      (by
                                        unfold nb074AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0011 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb074AlphaDummy000) ≠ (nb074AlphaDummy009) from
                                        (by
                                          unfold nb074AlphaDummy009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0007)
                                                  0)))) (show x ≠ (nb074AlphaDummy010 x) from
                                        (by
                                          unfold nb074AlphaDummy010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0009 x) 0))))
                                      (TAlphaVar.there (show (nb074AlphaDummy000) ≠
        (nb074AlphaDummy001) from (by
          unfold nb074AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0004) 0)))) (show x ≠ (nb074AlphaDummy002 x) from (by
          unfold nb074AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0005 x) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective (((Class.cv (nb074AlphaDummy000))).fv ∪
                                    ((Class.cv (nb074AlphaDummy001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb074AlphaDummy002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb074AlphaDummy006) ≠
        (nb074AlphaDummy013) from (by
          unfold nb074AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 0)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy015 x) from (by
          unfold nb074AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy006) ≠ (nb074AlphaDummy014) from (by
          unfold nb074AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 1)))) (show (nb074AlphaDummy008 x) ≠
        (nb074AlphaDummy016 x) from (by
          unfold nb074AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb074AlphaDummy006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠
        (nb074AlphaDummy020) from (by
          unfold
            nb074AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  1)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy023 x) from (by
          unfold
            nb074AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy019)
        from (by
          unfold
            nb074AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy022 x) from (by
          unfold
            nb074AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold
            nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold
            nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy021), (nb074AlphaDummy024 x)), ((nb074AlphaDummy020),
        (nb074AlphaDummy023 x)), ((nb074AlphaDummy019), (nb074AlphaDummy022 x)),
        ((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy006), (nb074AlphaDummy008 x)), ((nb074AlphaDummy005),
        (nb074AlphaDummy007 x)), ((nb074AlphaDummy011), (nb074AlphaDummy012 x)),
        ((nb074AlphaDummy009), (nb074AlphaDummy010 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy027) from (by
          unfold
            nb074AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy028 x) from (by
          unfold
            nb074AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy025)
        from (by
          unfold
            nb074AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy026 x) from (by
          unfold
            nb074AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy021), (nb074AlphaDummy024 x)), ((nb074AlphaDummy020),
        (nb074AlphaDummy023 x)), ((nb074AlphaDummy019), (nb074AlphaDummy022 x)),
        ((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy006), (nb074AlphaDummy008 x)), ((nb074AlphaDummy005),
        (nb074AlphaDummy007 x)), ((nb074AlphaDummy011), (nb074AlphaDummy012 x)),
        ((nb074AlphaDummy009), (nb074AlphaDummy010 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy013))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy020) ≠
        (nb074AlphaDummy031) from (by
          unfold
            nb074AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy032 x) from (by
          unfold
            nb074AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy020) ≠
        (nb074AlphaDummy031) from (by
          unfold
            nb074AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy032 x) from (by
          unfold
            nb074AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy020) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074AlphaDummy023 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy013))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy015 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy033) from (by
          unfold
            nb074AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy034 x) from (by
          unfold
            nb074AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy021) ≠
        (nb074AlphaDummy033) from (by
          unfold
            nb074AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy034 x) from (by
          unfold
            nb074AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy021) ≠ (nb074AlphaDummy029)
        from (by
          unfold
            nb074AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074AlphaDummy024 x) ≠ (nb074AlphaDummy030 x) from (by
          unfold
            nb074AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy006), (nb074AlphaDummy008 x)), ((nb074AlphaDummy005),
        (nb074AlphaDummy007 x)), ((nb074AlphaDummy011), (nb074AlphaDummy012 x)),
        ((nb074AlphaDummy009), (nb074AlphaDummy010 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017) from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014) 0)))) (show (nb074AlphaDummy015 x) ≠
        (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy013) ≠ (nb074AlphaDummy017)
        from (by
          unfold nb074AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074AlphaDummy015 x) ≠ (nb074AlphaDummy018 x) from (by
          unfold nb074AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy017), (nb074AlphaDummy018 x)), ((nb074AlphaDummy013),
        (nb074AlphaDummy015 x)), ((nb074AlphaDummy014), (nb074AlphaDummy016 x)),
        ((nb074AlphaDummy006), (nb074AlphaDummy008 x)), ((nb074AlphaDummy005),
        (nb074AlphaDummy007 x)), ((nb074AlphaDummy011), (nb074AlphaDummy012 x)),
        ((nb074AlphaDummy009), (nb074AlphaDummy010 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb074SplitAlpha0001 x)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
