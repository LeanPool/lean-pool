/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C073C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C073C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb073_split_alpha_0002`. -/
@[expose]
noncomputable def nb073SplitAlpha0002 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
        ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy012))
          (Class.cab (nb073AlphaDummy006) (synWrex (nb073AlphaDummy007)
              (synCop (Class.cv (nb073AlphaDummy000)) (Class.cv (nb073AlphaDummy001)))
              (Wff.classEq (Class.cv (nb073AlphaDummy006))
                (synCphi (Class.cv (nb073AlphaDummy007))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy012)) (Class.cab (nb073AlphaDummy006)
              (synWrex (nb073AlphaDummy007) (synCop (Class.cv (nb073AlphaDummy000))
                  (Class.cv (nb073AlphaDummy001)))
                (Wff.classEq (Class.cv (nb073AlphaDummy006))
                  (synCphi (Class.cv (nb073AlphaDummy007)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy013 x y))
          (Class.cab (nb073AlphaDummy008 x y)
            (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                (synCphi (Class.cv (nb073AlphaDummy009 x y))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy013 x y))
            (Class.cab (nb073AlphaDummy008 x y)
              (synWrex (nb073AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
                  (synCphi (Class.cv (nb073AlphaDummy009 x y))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb073SplitAlpha0000 x y dv_x_y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb073AlphaDummy001) ≠
        (nb073AlphaDummy015) from (by
          unfold nb073AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0050) 1)))) (show y ≠ (nb073AlphaDummy017 x y) from (by
          unfold nb073AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0052 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy001) ≠ (nb073AlphaDummy014) from (by
          unfold nb073AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0050) 0)))) (show y ≠ (nb073AlphaDummy016 x y) from (by
          unfold nb073AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0052 x y) 0)))) (TAlphaVar.there (show
        (nb073AlphaDummy001) ≠ (nb073AlphaDummy044) from (by
          unfold nb073AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0054) 0)))) (show y ≠ (nb073AlphaDummy045 x y) from (by
          unfold nb073AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0055 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy018)
        from (by
          unfold nb073AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0051) 0)))) (show y ≠ (nb073AlphaDummy019 x y) from (by
          unfold nb073AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0053 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy007)
        from (by
          unfold nb073AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0044)
                  1)))) (show y ≠ (nb073AlphaDummy009 x y) from (by
          unfold nb073AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0046 x y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy006)
        from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0044)
                  0)))) (show y ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0046 x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy012)
        from (by
          unfold nb073AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0048)
                  0)))) (show y ≠ (nb073AlphaDummy013 x y) from (by
          unfold nb073AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0049
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy010)
        from (by
          unfold nb073AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0045)
                  0)))) (show y ≠ (nb073AlphaDummy011 x y) from (by
          unfold nb073AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0047
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy002)
        from (by
          unfold
            nb073AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0042)
                  0)))) (show y ≠ (nb073AlphaDummy003 x y) from (by
          unfold
            nb073AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv)
        (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb073SplitAlpha0001 x y)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb073AlphaDummy001) ≠
        (nb073AlphaDummy015) from (by
          unfold nb073AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0050) 1)))) (show y ≠ (nb073AlphaDummy017 x y) from (by
          unfold nb073AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0052 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy001) ≠ (nb073AlphaDummy014) from (by
          unfold nb073AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0050) 0)))) (show y ≠ (nb073AlphaDummy016 x y) from (by
          unfold nb073AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0052 x y) 0)))) (TAlphaVar.there (show
        (nb073AlphaDummy001) ≠ (nb073AlphaDummy044) from (by
          unfold nb073AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0054) 0)))) (show y ≠ (nb073AlphaDummy045 x y) from (by
          unfold nb073AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0055 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy018)
        from (by
          unfold nb073AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0051) 0)))) (show y ≠ (nb073AlphaDummy019 x y) from (by
          unfold nb073AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0053 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy007)
        from (by
          unfold nb073AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0044)
                  1)))) (show y ≠ (nb073AlphaDummy009 x y) from (by
          unfold nb073AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0046 x y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy006)
        from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0044)
                  0)))) (show y ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0046 x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy012)
        from (by
          unfold nb073AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0048)
                  0)))) (show y ≠ (nb073AlphaDummy013 x y) from (by
          unfold nb073AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0049
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy010)
        from (by
          unfold nb073AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0045)
                  0)))) (show y ≠ (nb073AlphaDummy011 x y) from (by
          unfold nb073AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0047
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy002)
        from (by
          unfold
            nb073AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0042)
                  0)))) (show y ≠ (nb073AlphaDummy003 x y) from (by
          unfold
            nb073AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb073AlphaDummy000))).fv ∪ ((Class.cv (nb073AlphaDummy001))).fv)
        (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb073SplitAlpha0001 x y))))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((synCop (Class.cv (nb073AlphaDummy000))
                          (Class.cv (nb073AlphaDummy001)))).fv ∪
                      ((Class.cv (nb073AlphaDummy002))).fv) (by decide)) (freshVar_injective
                    (((synCop (Class.cv x) (Class.cv y))).fv ∪
                      ((Class.cv (nb073AlphaDummy003 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073AlphaDummy007) ≠ (nb073AlphaDummy050) from (by
                              unfold nb073AlphaDummy050;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0060) 0))))
                          (show (nb073AlphaDummy009 x y) ≠ (nb073AlphaDummy052 x y) from
                            (by
                              unfold nb073AlphaDummy052;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0061 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073AlphaDummy007) ≠ (nb073AlphaDummy051) from (by
                                unfold nb073AlphaDummy051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0060) 1)))) (show
                              (nb073AlphaDummy009 x y) ≠ (nb073AlphaDummy053 x y) from (by
                                unfold nb073AlphaDummy053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0061 x y) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073AlphaDummy007))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073AlphaDummy009 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy057) from (by
          unfold nb073AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0064) 1)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy060 x y) from (by
          unfold nb073AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0065 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy050) ≠ (nb073AlphaDummy056) from (by
          unfold nb073AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0064) 0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy059 x y) from (by
          unfold nb073AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0065 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054)
        from (by
          unfold nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062) 0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy055 x y) from (by
          unfold nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy058), (nb073AlphaDummy061 x y)), ((nb073AlphaDummy057),
        (nb073AlphaDummy060 x y)), ((nb073AlphaDummy056), (nb073AlphaDummy059 x y)),
        ((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006),
        (nb073AlphaDummy008 x y)), ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0068)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0069
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0066)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0067
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy064)
        from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0072)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0073
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0070)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0071
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0068)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0069
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0066)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0067
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy064)
        from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0072)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0073
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0070)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0071
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy058), (nb073AlphaDummy061 x y)), ((nb073AlphaDummy057),
        (nb073AlphaDummy060 x y)), ((nb073AlphaDummy056), (nb073AlphaDummy059 x y)),
        ((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006),
        (nb073AlphaDummy008 x y)), ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy050))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy057) ≠
        (nb073AlphaDummy068) from (by
          unfold
            nb073AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0076)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy069 x y) from (by
          unfold
            nb073AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0077
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0074)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0075
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy068)
        from (by
          unfold
            nb073AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0076)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy069 x y) from (by
          unfold
            nb073AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0077
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0074)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0075
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy070) from (by
          unfold
            nb073AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0080)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy071 x y) from (by
          unfold
            nb073AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0081
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0078)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0079
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠
        (nb073AlphaDummy070) from (by
          unfold
            nb073AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0080)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy071 x y) from (by
          unfold
            nb073AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0081
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0078)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0079
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from (by
                                        unfold nb073AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0062)
                                                0)))) (show (nb073AlphaDummy052 x y) ≠
                                        (nb073AlphaDummy055 x y) from (by
                                        unfold nb073AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0063 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy054), (nb073AlphaDummy055 x y)),
                                    ((nb073AlphaDummy050), (nb073AlphaDummy052 x y)),
                                    ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
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
                                  (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from
                                    (by
                                      unfold nb073AlphaDummy054;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0062)
                                              0)))) (show (nb073AlphaDummy052 x y) ≠
                                      (nb073AlphaDummy055 x y) from (by
                                      unfold nb073AlphaDummy055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0063 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from (by
                                        unfold nb073AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0062)
                                                0)))) (show (nb073AlphaDummy052 x y) ≠
                                        (nb073AlphaDummy055 x y) from (by
                                        unfold nb073AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0063 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy054), (nb073AlphaDummy055 x y)),
                                    ((nb073AlphaDummy050), (nb073AlphaDummy052 x y)),
                                    ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
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
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb073SplitAlpha0000 x y dv_x_y)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy015) from (by
          unfold nb073AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0050) 1)))) (show y ≠ (nb073AlphaDummy017 x y) from (by
          unfold nb073AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0052 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy001) ≠ (nb073AlphaDummy014) from (by
          unfold nb073AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0050) 0)))) (show y ≠ (nb073AlphaDummy016 x y) from (by
          unfold nb073AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0052 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy044)
        from (by
          unfold nb073AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0054) 0)))) (show y ≠ (nb073AlphaDummy045 x y) from (by
          unfold nb073AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0055 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy018)
        from (by
          unfold nb073AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0051)
                  0)))) (show y ≠ (nb073AlphaDummy019 x y) from (by
          unfold nb073AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0053 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy007)
        from (by
          unfold nb073AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0044)
                  1)))) (show y ≠ (nb073AlphaDummy009 x y) from (by
          unfold nb073AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0046 x
                    y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy006)
        from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0044)
                  0)))) (show y ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0046
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy012)
        from (by
          unfold nb073AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0048)
                  0)))) (show y ≠ (nb073AlphaDummy013 x y) from (by
          unfold nb073AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0049
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy010)
        from (by
          unfold
            nb073AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0045)
                  0)))) (show y ≠ (nb073AlphaDummy011 x y) from (by
          unfold
            nb073AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0047
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy002)
        from (by
          unfold
            nb073AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0042)
                  0)))) (show y ≠ (nb073AlphaDummy003 x y) from (by
          unfold
            nb073AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy000))).fv ∪
        ((Class.cv (nb073AlphaDummy001))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb073SplitAlpha0001 x y)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy015) from (by
          unfold nb073AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0050) 1)))) (show y ≠ (nb073AlphaDummy017 x y) from (by
          unfold nb073AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0052 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy001) ≠ (nb073AlphaDummy014) from (by
          unfold nb073AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0050) 0)))) (show y ≠ (nb073AlphaDummy016 x y) from (by
          unfold nb073AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0052 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy044)
        from (by
          unfold nb073AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0054) 0)))) (show y ≠ (nb073AlphaDummy045 x y) from (by
          unfold nb073AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0055 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy018)
        from (by
          unfold nb073AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0051)
                  0)))) (show y ≠ (nb073AlphaDummy019 x y) from (by
          unfold nb073AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0053 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy007)
        from (by
          unfold nb073AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0044)
                  1)))) (show y ≠ (nb073AlphaDummy009 x y) from (by
          unfold nb073AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0046 x
                    y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy006)
        from (by
          unfold nb073AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0044)
                  0)))) (show y ≠ (nb073AlphaDummy008 x y) from (by
          unfold nb073AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0046
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy012)
        from (by
          unfold nb073AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0048)
                  0)))) (show y ≠ (nb073AlphaDummy013 x y) from (by
          unfold nb073AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0049
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy010)
        from (by
          unfold
            nb073AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0045)
                  0)))) (show y ≠ (nb073AlphaDummy011 x y) from (by
          unfold
            nb073AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0047
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy002)
        from (by
          unfold
            nb073AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0042)
                  0)))) (show y ≠ (nb073AlphaDummy003 x y) from (by
          unfold
            nb073AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy000))).fv ∪
        ((Class.cv (nb073AlphaDummy001))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb073SplitAlpha0001 x y))))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((synCop (Class.cv (nb073AlphaDummy000))
                            (Class.cv (nb073AlphaDummy001)))).fv ∪
                        ((Class.cv (nb073AlphaDummy002))).fv) (by decide))
                    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
                        ((Class.cv (nb073AlphaDummy003 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb073AlphaDummy007) ≠ (nb073AlphaDummy050) from (by
                                unfold nb073AlphaDummy050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0060) 0)))) (show
                              (nb073AlphaDummy009 x y) ≠ (nb073AlphaDummy052 x y) from (by
                                unfold nb073AlphaDummy052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0061 x y) 0))))
                            (TAlphaVar.there
                              (show (nb073AlphaDummy007) ≠ (nb073AlphaDummy051) from (by
                                  unfold nb073AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0060) 1)))) (show
                                (nb073AlphaDummy009 x y) ≠ (nb073AlphaDummy053 x y) from
                                (by
                                  unfold nb073AlphaDummy053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0061 x y)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb073AlphaDummy007))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb073AlphaDummy009 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb073AlphaDummy050) ≠ (nb073AlphaDummy057) from (by
          unfold nb073AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0064) 1)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy060 x y) from (by
          unfold nb073AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0065 x y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy056)
        from (by
          unfold nb073AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0064) 0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy059 x y) from (by
          unfold nb073AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0065 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054)
        from (by
          unfold nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062)
                  0)))) (show (nb073AlphaDummy052 x y) ≠ (nb073AlphaDummy055 x y) from (by
          unfold nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy058), (nb073AlphaDummy061 x y)), ((nb073AlphaDummy057),
        (nb073AlphaDummy060 x y)), ((nb073AlphaDummy056), (nb073AlphaDummy059 x y)),
        ((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006),
        (nb073AlphaDummy008 x y)), ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0068)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0069
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0066)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0067
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy064)
        from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0072)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0073
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0070)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0071
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0068)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0069
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0066)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0067
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy064)
        from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0072)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0073
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0070)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0071
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy058), (nb073AlphaDummy061 x y)), ((nb073AlphaDummy057),
        (nb073AlphaDummy060 x y)), ((nb073AlphaDummy056), (nb073AlphaDummy059 x y)),
        ((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)), ((nb073AlphaDummy006),
        (nb073AlphaDummy008 x y)), ((nb073AlphaDummy012), (nb073AlphaDummy013 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy050))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy057) ≠
        (nb073AlphaDummy068) from (by
          unfold
            nb073AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0076)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy069 x y) from (by
          unfold
            nb073AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0077
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0074)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0075
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy068)
        from (by
          unfold
            nb073AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0076)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy069 x y) from (by
          unfold
            nb073AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0077
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0074)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0075
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy070) from (by
          unfold
            nb073AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0080)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy071 x y) from (by
          unfold
            nb073AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0081
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0078)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0079
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠
        (nb073AlphaDummy070) from (by
          unfold
            nb073AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0080)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy071 x y) from (by
          unfold
            nb073AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0081
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0078)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0079
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from
                                        (by
                                          unfold nb073AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0062)
                                                  0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy055 x y) from (by
                                          unfold nb073AlphaDummy055;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0063 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb073AlphaDummy054), (nb073AlphaDummy055 x y)),
                                      ((nb073AlphaDummy050), (nb073AlphaDummy052 x y)),
                                      ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
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
                                      (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from (by
                                        unfold nb073AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0062)
                                                0)))) (show (nb073AlphaDummy052 x y) ≠
                                        (nb073AlphaDummy055 x y) from (by
                                        unfold nb073AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0063 x y) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from
                                        (by
                                          unfold nb073AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0062)
                                                  0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy055 x y) from (by
                                          unfold nb073AlphaDummy055;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0063 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb073AlphaDummy054), (nb073AlphaDummy055 x y)),
                                      ((nb073AlphaDummy050), (nb073AlphaDummy052 x y)),
                                      ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
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

/-! Certificates from `NAR4C073C001Part007`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb073_split_alpha_0003`. -/
@[expose]
noncomputable def nb073SplitAlpha0003 (x : Var) (y : Var) :
    TAlphaWff
      [((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
        ((nb073AlphaDummy072), (nb073AlphaDummy073 x y)),
        ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
        ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy007))
          (Class.cv (nb073AlphaDummy002))) (Wff.neg
          (Wff.classEq (Class.cv (nb073AlphaDummy006))
            (synCun (synCphi (Class.cv (nb073AlphaDummy007))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy009 x y))
          (Class.cv (nb073AlphaDummy003 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb073AlphaDummy008 x y))
            (synCun (synCphi (Class.cv (nb073AlphaDummy009 x y)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy002) ≠ (nb073AlphaDummy007) from (by
              unfold nb073AlphaDummy007;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 1))))
          (show (nb073AlphaDummy003 x y) ≠ (nb073AlphaDummy009 x y) from (by
              unfold nb073AlphaDummy009;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 1))))
          (TAlphaVar.there (show (nb073AlphaDummy002) ≠ (nb073AlphaDummy006) from (by
                unfold nb073AlphaDummy006;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 0))))
            (show (nb073AlphaDummy003 x y) ≠ (nb073AlphaDummy008 x y) from (by
                unfold nb073AlphaDummy008;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 0))))
            (TAlphaVar.there (show (nb073AlphaDummy002) ≠ (nb073AlphaDummy072) from (by
                  unfold nb073AlphaDummy072;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0086) 0))))
              (show (nb073AlphaDummy003 x y) ≠ (nb073AlphaDummy073 x y) from (by
                  unfold nb073AlphaDummy073;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0087 x y) 0))))
              (TAlphaVar.there (show (nb073AlphaDummy002) ≠ (nb073AlphaDummy010) from (by
                    unfold nb073AlphaDummy010;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0083) 0))))
                (show (nb073AlphaDummy003 x y) ≠ (nb073AlphaDummy011 x y) from (by
                    unfold nb073AlphaDummy011;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0085 x y) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((synCop (Class.cv (nb073AlphaDummy000))
                    (Class.cv (nb073AlphaDummy001)))).fv ∪
                ((Class.cv (nb073AlphaDummy002))).fv) (by decide)) (freshVar_injective
              (((synCop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb073AlphaDummy003 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy007) ≠ (nb073AlphaDummy050) from (by
                                        unfold nb073AlphaDummy050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0060)
                                                0)))) (show (nb073AlphaDummy009 x y) ≠
                                        (nb073AlphaDummy052 x y) from (by
                                        unfold nb073AlphaDummy052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0061 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb073AlphaDummy007) ≠ (nb073AlphaDummy051) from
                                        (by
                                          unfold nb073AlphaDummy051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0060)
                                                  1)))) (show (nb073AlphaDummy009 x y) ≠
        (nb073AlphaDummy053 x y) from (by
                                          unfold nb073AlphaDummy053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0061 x y) 1))))
                                      (TAlphaVar.there (show (nb073AlphaDummy007) ≠
        (nb073AlphaDummy076) from (by
          unfold nb073AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0090) 0)))) (show (nb073AlphaDummy009 x y) ≠
        (nb073AlphaDummy077 x y) from (by
          unfold nb073AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0091 x y) 0)))) (TAlphaVar.there (show
        (nb073AlphaDummy007) ≠ (nb073AlphaDummy074) from (by
          unfold nb073AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0088) 0)))) (show (nb073AlphaDummy009 x y) ≠
        (nb073AlphaDummy075 x y) from (by
          unfold nb073AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0089 x y) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb073AlphaDummy007))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb073AlphaDummy009 x y))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy057) from (by
          unfold nb073AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0064)
                  1)))) (show (nb073AlphaDummy052 x y) ≠ (nb073AlphaDummy060 x y) from (by
          unfold nb073AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0065
                    x y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy056)
        from (by
          unfold nb073AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0064)
                  0)))) (show (nb073AlphaDummy052 x y) ≠ (nb073AlphaDummy059 x y) from (by
          unfold nb073AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054)
        from (by
          unfold
            nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062)
                  0)))) (show (nb073AlphaDummy052 x y) ≠ (nb073AlphaDummy055 x y) from (by
          unfold
            nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy058), (nb073AlphaDummy061 x y)), ((nb073AlphaDummy057),
        (nb073AlphaDummy060 x y)), ((nb073AlphaDummy056), (nb073AlphaDummy059 x y)),
        ((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy076), (nb073AlphaDummy077 x y)), ((nb073AlphaDummy074),
        (nb073AlphaDummy075 x y)), ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)), ((nb073AlphaDummy072),
        (nb073AlphaDummy073 x y)), ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0068)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0066)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠
        (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0072)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0070)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0068)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0066)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠
        (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0072)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0070)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy058), (nb073AlphaDummy061 x y)), ((nb073AlphaDummy057),
        (nb073AlphaDummy060 x y)), ((nb073AlphaDummy056), (nb073AlphaDummy059 x y)),
        ((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy076), (nb073AlphaDummy077 x y)), ((nb073AlphaDummy074),
        (nb073AlphaDummy075 x y)), ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)), ((nb073AlphaDummy072),
        (nb073AlphaDummy073 x y)), ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy050))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052
        x y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy057) ≠
        (nb073AlphaDummy068) from (by
          unfold
            nb073AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0076)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy069 x y) from (by
          unfold
            nb073AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0074)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy057) ≠
        (nb073AlphaDummy068) from (by
          unfold
            nb073AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0076)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy069 x y) from (by
          unfold
            nb073AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0074)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy070) from (by
          unfold
            nb073AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0080)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy071 x y) from (by
          unfold
            nb073AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0078)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠
        (nb073AlphaDummy070) from (by
          unfold
            nb073AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0080)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy071 x y) from (by
          unfold
            nb073AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0078)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054)
        from (by
          unfold nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062) 0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy055 x y) from (by
          unfold nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy076), (nb073AlphaDummy077 x y)), ((nb073AlphaDummy074),
        (nb073AlphaDummy075 x y)), ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)), ((nb073AlphaDummy072),
        (nb073AlphaDummy073 x y)), ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from (by
          unfold nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062) 0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy055 x y) from (by
          unfold nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from (by
          unfold nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062) 0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy055 x y) from (by
          unfold nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy076), (nb073AlphaDummy077 x y)), ((nb073AlphaDummy074),
        (nb073AlphaDummy075 x y)), ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)), ((nb073AlphaDummy072),
        (nb073AlphaDummy073 x y)), ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy007) ≠ (nb073AlphaDummy050) from (by
                                        unfold nb073AlphaDummy050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0060)
                                                0)))) (show (nb073AlphaDummy009 x y) ≠
                                        (nb073AlphaDummy052 x y) from (by
                                        unfold nb073AlphaDummy052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0061 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb073AlphaDummy007) ≠ (nb073AlphaDummy051) from
                                        (by
                                          unfold nb073AlphaDummy051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0060)
                                                  1)))) (show (nb073AlphaDummy009 x y) ≠
        (nb073AlphaDummy053 x y) from (by
                                          unfold nb073AlphaDummy053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0061 x y) 1))))
                                      (TAlphaVar.there (show (nb073AlphaDummy007) ≠
        (nb073AlphaDummy076) from (by
          unfold nb073AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0090) 0)))) (show (nb073AlphaDummy009 x y) ≠
        (nb073AlphaDummy077 x y) from (by
          unfold nb073AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0091 x y) 0)))) (TAlphaVar.there (show
        (nb073AlphaDummy007) ≠ (nb073AlphaDummy074) from (by
          unfold nb073AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0088) 0)))) (show (nb073AlphaDummy009 x y) ≠
        (nb073AlphaDummy075 x y) from (by
          unfold nb073AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0089 x y) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb073AlphaDummy007))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb073AlphaDummy009 x y))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy057) from (by
          unfold nb073AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0064)
                  1)))) (show (nb073AlphaDummy052 x y) ≠ (nb073AlphaDummy060 x y) from (by
          unfold nb073AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0065
                    x y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy056)
        from (by
          unfold nb073AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0064)
                  0)))) (show (nb073AlphaDummy052 x y) ≠ (nb073AlphaDummy059 x y) from (by
          unfold nb073AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054)
        from (by
          unfold
            nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062)
                  0)))) (show (nb073AlphaDummy052 x y) ≠ (nb073AlphaDummy055 x y) from (by
          unfold
            nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy058), (nb073AlphaDummy061 x y)), ((nb073AlphaDummy057),
        (nb073AlphaDummy060 x y)), ((nb073AlphaDummy056), (nb073AlphaDummy059 x y)),
        ((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy076), (nb073AlphaDummy077 x y)), ((nb073AlphaDummy074),
        (nb073AlphaDummy075 x y)), ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)), ((nb073AlphaDummy072),
        (nb073AlphaDummy073 x y)), ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0068)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0066)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠
        (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0072)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0070)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0068)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0066)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠
        (nb073AlphaDummy064) from (by
          unfold
            nb073AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0072)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy065 x y) from (by
          unfold
            nb073AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy062)
        from (by
          unfold
            nb073AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0070)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy063 x y) from (by
          unfold
            nb073AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy058), (nb073AlphaDummy061 x y)), ((nb073AlphaDummy057),
        (nb073AlphaDummy060 x y)), ((nb073AlphaDummy056), (nb073AlphaDummy059 x y)),
        ((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy076), (nb073AlphaDummy077 x y)), ((nb073AlphaDummy074),
        (nb073AlphaDummy075 x y)), ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)), ((nb073AlphaDummy072),
        (nb073AlphaDummy073 x y)), ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy050))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052
        x y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy057) ≠
        (nb073AlphaDummy068) from (by
          unfold
            nb073AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0076)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy069 x y) from (by
          unfold
            nb073AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0074)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy057) ≠
        (nb073AlphaDummy068) from (by
          unfold
            nb073AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0076)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy069 x y) from (by
          unfold
            nb073AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy057) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0074)
                  0)))) (show (nb073AlphaDummy060 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy070) from (by
          unfold
            nb073AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0080)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy071 x y) from (by
          unfold
            nb073AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0078)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy058) ≠
        (nb073AlphaDummy070) from (by
          unfold
            nb073AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0080)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy071 x y) from (by
          unfold
            nb073AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy058) ≠ (nb073AlphaDummy066)
        from (by
          unfold
            nb073AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0078)
                  0)))) (show (nb073AlphaDummy061 x y) ≠ (nb073AlphaDummy067 x y) from (by
          unfold
            nb073AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054)
        from (by
          unfold nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062) 0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy055 x y) from (by
          unfold nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy076), (nb073AlphaDummy077 x y)), ((nb073AlphaDummy074),
        (nb073AlphaDummy075 x y)), ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)), ((nb073AlphaDummy072),
        (nb073AlphaDummy073 x y)), ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from (by
          unfold nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062) 0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy055 x y) from (by
          unfold nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb073AlphaDummy050) ≠ (nb073AlphaDummy054) from (by
          unfold nb073AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0062) 0)))) (show (nb073AlphaDummy052 x y) ≠
        (nb073AlphaDummy055 x y) from (by
          unfold nb073AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy054), (nb073AlphaDummy055 x y)), ((nb073AlphaDummy050),
        (nb073AlphaDummy052 x y)), ((nb073AlphaDummy051), (nb073AlphaDummy053 x y)),
        ((nb073AlphaDummy076), (nb073AlphaDummy077 x y)), ((nb073AlphaDummy074),
        (nb073AlphaDummy075 x y)), ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
        ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)), ((nb073AlphaDummy072),
        (nb073AlphaDummy073 x y)), ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb073AlphaDummy074), (nb073AlphaDummy075 x y)),
                    ((nb073AlphaDummy007), (nb073AlphaDummy009 x y)),
                    ((nb073AlphaDummy006), (nb073AlphaDummy008 x y)),
                    ((nb073AlphaDummy072), (nb073AlphaDummy073 x y)),
                    ((nb073AlphaDummy010), (nb073AlphaDummy011 x y)),
                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
