/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C089C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C089C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb089_split_alpha_0002`. -/
@[expose]
noncomputable def nb089SplitAlpha0002 (u : Var) (A : Class) (B : Class) (R : Class) :
    TAlphaWff
      [((nb089AlphaDummy051 A B R), (nb089AlphaDummy052 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u),
        ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
        ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      (Wff.imp (Wff.classMem (Class.cv (nb089AlphaDummy051 A B R))
          (Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
              (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                (synCphi (Class.cv (nb089AlphaDummy046 A B R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb089AlphaDummy051 A B R))
            (Class.cab (nb089AlphaDummy045 A B R) (synWrex (nb089AlphaDummy046 A B R)
                (synCsn (Class.cv (nb089AlphaDummy043 A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
                  (synCphi (Class.cv (nb089AlphaDummy046 A B R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb089AlphaDummy052 u A B R))
          (Class.cab (nb089AlphaDummy047 u A B R) (synWrex (nb089AlphaDummy048 u A B R)
              (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
              (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb089AlphaDummy052 u A B R))
            (Class.cab (nb089AlphaDummy047 u A B R) (synWrex (nb089AlphaDummy048 u A B R)
                (synCsn (Class.cv (nb089AlphaDummy044 u A B R)))
                (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
                  (synCphi (Class.cv (nb089AlphaDummy048 u A B R))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy053 A B R) from
                        (by
                          unfold nb089AlphaDummy053;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb089_support_mem_0050 A B R) 0)))) (show
                        (nb089AlphaDummy044 u A B R) ≠ (nb089AlphaDummy054 u A B R) from
                        (by
                          unfold nb089AlphaDummy054;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb089_support_mem_0051 u A B R) 0))))
                      (TAlphaVar.there (show
                          (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy046 A B R) from (by
                            unfold nb089AlphaDummy046;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1)))) (show
                          (nb089AlphaDummy044 u A B R) ≠ (nb089AlphaDummy048 u A B R) from
                          (by
                            unfold nb089AlphaDummy048;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 1))))
                        (TAlphaVar.there (show
                            (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy045 A B R) from
                            (by
                              unfold nb089AlphaDummy045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0044 A B R) 0)))) (show
                            (nb089AlphaDummy044 u A B R) ≠ (nb089AlphaDummy047 u A B R)
                            from (by
                              unfold nb089AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0046 u A B R)
                                      0)))) (TAlphaVar.there (show
                              (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy051 A B R) from
                              (by
                                unfold nb089AlphaDummy051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0048 A B R)
                                        0)))) (show (nb089AlphaDummy044 u A B R) ≠
                                (nb089AlphaDummy052 u A B R) from (by
                                unfold nb089AlphaDummy052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0049 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy049 A B R)
                                from (by
                                  unfold nb089AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0045 A B R)
                                          0)))) (show (nb089AlphaDummy044 u A B R) ≠
                                  (nb089AlphaDummy050 u A B R) from (by
                                  unfold nb089AlphaDummy050;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0047 u A B R)
                                          0)))) (TAlphaVar.here _ _ _))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
                      ((Class.cv (nb089AlphaDummy000 A B R))).fv) (by decide))
                  (freshVar_injective
                    (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪
                      ((Class.cv u)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show
                            (nb089AlphaDummy046 A B R) ≠ (nb089AlphaDummy055 A B R) from
                            (by
                              unfold nb089AlphaDummy055;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0052 A B R) 0)))) (show
                            (nb089AlphaDummy048 u A B R) ≠ (nb089AlphaDummy057 u A B R)
                            from (by
                              unfold nb089AlphaDummy057;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0053 u A B R)
                                      0)))) (TAlphaVar.there (show
                              (nb089AlphaDummy046 A B R) ≠ (nb089AlphaDummy056 A B R) from
                              (by
                                unfold nb089AlphaDummy056;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0052 A B R)
                                        1)))) (show (nb089AlphaDummy048 u A B R) ≠
                                (nb089AlphaDummy058 u A B R) from (by
                                unfold nb089AlphaDummy058;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0053 u A B R)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb089AlphaDummy046 A B R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb089AlphaDummy048 u A B R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠ (nb089AlphaDummy062 A B R)
        from (by
          unfold nb089AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056 A B R)
                  1)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy065 u A B R)
        from (by
          unfold nb089AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057 u A B R)
                  1)))) (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy061 A B R) from (by
          unfold nb089AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056 A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy064 u A B R)
        from (by
          unfold nb089AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057 u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
          unfold nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy063 A B R), (nb089AlphaDummy066 u A B R)),
        ((nb089AlphaDummy062 A B R), (nb089AlphaDummy065 u A B R)),
        ((nb089AlphaDummy061 A B R), (nb089AlphaDummy064 u A B R)),
        ((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy051 A B R), (nb089AlphaDummy052 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy062
        A B R) ≠ (nb089AlphaDummy069 A B R) from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u A B R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠ (nb089AlphaDummy069 A B R)
        from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠ (nb089AlphaDummy069 A B R)
        from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u A B R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠ (nb089AlphaDummy069 A B R)
        from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy063 A B R), (nb089AlphaDummy066 u A B R)),
        ((nb089AlphaDummy062 A B R), (nb089AlphaDummy065 u A B R)),
        ((nb089AlphaDummy061 A B R), (nb089AlphaDummy064 u A B R)),
        ((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy051 A B R), (nb089AlphaDummy052 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy062
        A B R) ≠ (nb089AlphaDummy073 A B R) from (by
          unfold
            nb089AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy074 u A B R)
        from (by
          unfold
            nb089AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u A B R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠ (nb089AlphaDummy073 A B R)
        from (by
          unfold
            nb089AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy074 u A B R)
        from (by
          unfold
            nb089AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u A B R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy075 A B R) from (by
          unfold
            nb089AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy076 u A B R)
        from (by
          unfold
            nb089AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy075 A B R) from (by
          unfold
            nb089AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy076 u A B R)
        from (by
          unfold
            nb089AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089AlphaDummy055 A B R) ≠
                                        (nb089AlphaDummy059 A B R) from (by
                                        unfold nb089AlphaDummy059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0054 A B R) 0)))) (show
                                      (nb089AlphaDummy057 u A B R) ≠
                                        (nb089AlphaDummy060 u A B R) from (by
                                        unfold nb089AlphaDummy060;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0055 u A B R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb089AlphaDummy059 A B R),
                                      (nb089AlphaDummy060 u A B R)),
                                    ((nb089AlphaDummy055 A B R),
                                      (nb089AlphaDummy057 u A B R)),
                                    ((nb089AlphaDummy056 A B R),
                                      (nb089AlphaDummy058 u A B R)),
                                    ((nb089AlphaDummy046 A B R),
                                      (nb089AlphaDummy048 u A B R)),
                                    ((nb089AlphaDummy045 A B R),
                                      (nb089AlphaDummy047 u A B R)),
                                    ((nb089AlphaDummy051 A B R),
                                      (nb089AlphaDummy052 u A B R)),
                                    ((nb089AlphaDummy049 A B R),
                                      (nb089AlphaDummy050 u A B R)),
                                    ((nb089AlphaDummy043 A B R),
                                      (nb089AlphaDummy044 u A B R)),
                                    ((nb089AlphaDummy003 A B R),
                                      (nb089AlphaDummy004 u A B R)),
                                    ((nb089AlphaDummy000 A B R), u),
                                    ((nb089AlphaDummy005 A B R),
                                      (nb089AlphaDummy006 u A B R)),
                                    ((nb089AlphaDummy001 A B R),
                                      (nb089AlphaDummy002 u A B R))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb089AlphaDummy055 A B R) ≠
                                      (nb089AlphaDummy059 A B R) from (by
                                      unfold nb089AlphaDummy059;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0054 A B R) 0)))) (show
                                    (nb089AlphaDummy057 u A B R) ≠
                                      (nb089AlphaDummy060 u A B R) from (by
                                      unfold nb089AlphaDummy060;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0055 u A B R) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089AlphaDummy055 A B R) ≠
                                        (nb089AlphaDummy059 A B R) from (by
                                        unfold nb089AlphaDummy059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0054 A B R) 0)))) (show
                                      (nb089AlphaDummy057 u A B R) ≠
                                        (nb089AlphaDummy060 u A B R) from (by
                                        unfold nb089AlphaDummy060;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0055 u A B R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb089AlphaDummy059 A B R),
                                      (nb089AlphaDummy060 u A B R)),
                                    ((nb089AlphaDummy055 A B R),
                                      (nb089AlphaDummy057 u A B R)),
                                    ((nb089AlphaDummy056 A B R),
                                      (nb089AlphaDummy058 u A B R)),
                                    ((nb089AlphaDummy046 A B R),
                                      (nb089AlphaDummy048 u A B R)),
                                    ((nb089AlphaDummy045 A B R),
                                      (nb089AlphaDummy047 u A B R)),
                                    ((nb089AlphaDummy051 A B R),
                                      (nb089AlphaDummy052 u A B R)),
                                    ((nb089AlphaDummy049 A B R),
                                      (nb089AlphaDummy050 u A B R)),
                                    ((nb089AlphaDummy043 A B R),
                                      (nb089AlphaDummy044 u A B R)),
                                    ((nb089AlphaDummy003 A B R),
                                      (nb089AlphaDummy004 u A B R)),
                                    ((nb089AlphaDummy000 A B R), u),
                                    ((nb089AlphaDummy005 A B R),
                                      (nb089AlphaDummy006 u A B R)),
                                    ((nb089AlphaDummy001 A B R),
                                      (nb089AlphaDummy002 u A B R))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show
                          (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy053 A B R) from (by
                            unfold nb089AlphaDummy053;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb089_support_mem_0050 A B R) 0)))) (show
                          (nb089AlphaDummy044 u A B R) ≠ (nb089AlphaDummy054 u A B R) from
                          (by
                            unfold nb089AlphaDummy054;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb089_support_mem_0051 u A B R) 0))))
                        (TAlphaVar.there (show
                            (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy046 A B R) from
                            (by
                              unfold nb089AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1)))) (show
                            (nb089AlphaDummy044 u A B R) ≠ (nb089AlphaDummy048 u A B R)
                            from (by
                              unfold nb089AlphaDummy048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0046 u A B R)
                                      1)))) (TAlphaVar.there (show
                              (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy045 A B R) from
                              (by
                                unfold nb089AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0044 A B R)
                                        0)))) (show (nb089AlphaDummy044 u A B R) ≠
                                (nb089AlphaDummy047 u A B R) from (by
                                unfold nb089AlphaDummy047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0046 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy051 A B R)
                                from (by
                                  unfold nb089AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0048 A B R)
                                          0)))) (show (nb089AlphaDummy044 u A B R) ≠
                                  (nb089AlphaDummy052 u A B R) from (by
                                  unfold nb089AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0049 u A B R)
                                          0)))) (TAlphaVar.there (show
                                  (nb089AlphaDummy043 A B R) ≠ (nb089AlphaDummy049 A B R)
                                  from (by
                                    unfold nb089AlphaDummy049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb089_support_mem_0045 A B R)
                                            0)))) (show (nb089AlphaDummy044 u A B R) ≠
                                    (nb089AlphaDummy050 u A B R) from (by
                                    unfold nb089AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb089_support_mem_0047 u A B R) 0))))
                                (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
                        ((Class.cv (nb089AlphaDummy000 A B R))).fv) (by decide))
                    (freshVar_injective
                      (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪
                        ((Class.cv u)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy046 A B R) ≠
                                (nb089AlphaDummy055 A B R) from (by
                                unfold nb089AlphaDummy055;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0052 A B R)
                                        0)))) (show (nb089AlphaDummy048 u A B R) ≠
                                (nb089AlphaDummy057 u A B R) from (by
                                unfold nb089AlphaDummy057;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0053 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089AlphaDummy046 A B R) ≠ (nb089AlphaDummy056 A B R)
                                from (by
                                  unfold nb089AlphaDummy056;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0052 A B R)
                                          1)))) (show (nb089AlphaDummy048 u A B R) ≠
                                  (nb089AlphaDummy058 u A B R) from (by
                                  unfold nb089AlphaDummy058;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0053 u A B R)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb089AlphaDummy046 A B R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb089AlphaDummy048 u A B R))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb089AlphaDummy055 A B R) ≠ (nb089AlphaDummy062 A B R) from (by
          unfold nb089AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056 A B R)
                  1)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy065 u A B R)
        from (by
          unfold nb089AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057 u A B R)
                  1)))) (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy061 A B R) from (by
          unfold nb089AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056 A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy064 u A B R)
        from (by
          unfold nb089AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057 u A B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
          unfold nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B
                    R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A
                    B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy063 A B R), (nb089AlphaDummy066 u A B R)),
        ((nb089AlphaDummy062 A B R), (nb089AlphaDummy065 u A B R)),
        ((nb089AlphaDummy061 A B R), (nb089AlphaDummy064 u A B R)),
        ((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy051 A B R), (nb089AlphaDummy052 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy062
        A B R) ≠ (nb089AlphaDummy069 A B R) from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u A B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠ (nb089AlphaDummy069 A B R)
        from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠ (nb089AlphaDummy069 A B R)
        from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u A B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠ (nb089AlphaDummy069 A B R)
        from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy063 A B R), (nb089AlphaDummy066 u A B R)),
        ((nb089AlphaDummy062 A B R), (nb089AlphaDummy065 u A B R)),
        ((nb089AlphaDummy061 A B R), (nb089AlphaDummy064 u A B R)),
        ((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy051 A B R), (nb089AlphaDummy052 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy062
        A B R) ≠ (nb089AlphaDummy073 A B R) from (by
          unfold
            nb089AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy074 u A B R)
        from (by
          unfold
            nb089AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u A B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠ (nb089AlphaDummy073 A B R)
        from (by
          unfold
            nb089AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy074 u A B R)
        from (by
          unfold
            nb089AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A B R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u A B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy075 A B R) from (by
          unfold
            nb089AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy076 u A B R)
        from (by
          unfold
            nb089AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy075 A B R) from (by
          unfold
            nb089AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy076 u A B R)
        from (by
          unfold
            nb089AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A B R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
                                          unfold nb089AlphaDummy059;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0054 A B R) 0)))) (show
                                        (nb089AlphaDummy057 u A B R) ≠
        (nb089AlphaDummy060 u A B R) from (by
                                          unfold nb089AlphaDummy060;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0055 u A B R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb089AlphaDummy059 A B R),
                                        (nb089AlphaDummy060 u A B R)),
                                      ((nb089AlphaDummy055 A B R),
                                        (nb089AlphaDummy057 u A B R)),
                                      ((nb089AlphaDummy056 A B R),
                                        (nb089AlphaDummy058 u A B R)),
                                      ((nb089AlphaDummy046 A B R),
                                        (nb089AlphaDummy048 u A B R)),
                                      ((nb089AlphaDummy045 A B R),
                                        (nb089AlphaDummy047 u A B R)),
                                      ((nb089AlphaDummy051 A B R),
                                        (nb089AlphaDummy052 u A B R)),
                                      ((nb089AlphaDummy049 A B R),
                                        (nb089AlphaDummy050 u A B R)),
                                      ((nb089AlphaDummy043 A B R),
                                        (nb089AlphaDummy044 u A B R)),
                                      ((nb089AlphaDummy003 A B R),
                                        (nb089AlphaDummy004 u A B R)),
                                      ((nb089AlphaDummy000 A B R), u),
                                      ((nb089AlphaDummy005 A B R),
                                        (nb089AlphaDummy006 u A B R)),
                                      ((nb089AlphaDummy001 A B R),
                                        (nb089AlphaDummy002 u A B R))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089AlphaDummy055 A B R) ≠
                                        (nb089AlphaDummy059 A B R) from (by
                                        unfold nb089AlphaDummy059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0054 A B R) 0)))) (show
                                      (nb089AlphaDummy057 u A B R) ≠
                                        (nb089AlphaDummy060 u A B R) from (by
                                        unfold nb089AlphaDummy060;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0055 u A B R) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
                                          unfold nb089AlphaDummy059;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0054 A B R) 0)))) (show
                                        (nb089AlphaDummy057 u A B R) ≠
        (nb089AlphaDummy060 u A B R) from (by
                                          unfold nb089AlphaDummy060;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0055 u A B R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb089AlphaDummy059 A B R),
                                        (nb089AlphaDummy060 u A B R)),
                                      ((nb089AlphaDummy055 A B R),
                                        (nb089AlphaDummy057 u A B R)),
                                      ((nb089AlphaDummy056 A B R),
                                        (nb089AlphaDummy058 u A B R)),
                                      ((nb089AlphaDummy046 A B R),
                                        (nb089AlphaDummy048 u A B R)),
                                      ((nb089AlphaDummy045 A B R),
                                        (nb089AlphaDummy047 u A B R)),
                                      ((nb089AlphaDummy051 A B R),
                                        (nb089AlphaDummy052 u A B R)),
                                      ((nb089AlphaDummy049 A B R),
                                        (nb089AlphaDummy050 u A B R)),
                                      ((nb089AlphaDummy043 A B R),
                                        (nb089AlphaDummy044 u A B R)),
                                      ((nb089AlphaDummy003 A B R),
                                        (nb089AlphaDummy004 u A B R)),
                                      ((nb089AlphaDummy000 A B R), u),
                                      ((nb089AlphaDummy005 A B R),
                                        (nb089AlphaDummy006 u A B R)),
                                      ((nb089AlphaDummy001 A B R),
                                        (nb089AlphaDummy002 u A B R))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C089C001Part007`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb089_split_alpha_0003`. -/
@[expose]
noncomputable def nb089SplitAlpha0003 (u : Var) (A : Class) (B : Class) (R : Class) :
    TAlphaWff
      [((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u),
        ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
        ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      (Wff.imp (Wff.classMem (Class.cv (nb089AlphaDummy046 A B R))
          (Class.cv (nb089AlphaDummy000 A B R))) (Wff.neg
          (Wff.classEq (Class.cv (nb089AlphaDummy045 A B R))
            (synCun (synCphi (Class.cv (nb089AlphaDummy046 A B R))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb089AlphaDummy048 u A B R)) (Class.cv u)) (Wff.neg
          (Wff.classEq (Class.cv (nb089AlphaDummy047 u A B R))
            (synCun (synCphi (Class.cv (nb089AlphaDummy048 u A B R)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy046 A B R) from (by
              unfold nb089AlphaDummy046;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 1))))
          (show u ≠ (nb089AlphaDummy048 u A B R) from (by
              unfold nb089AlphaDummy048;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 1))))
          (TAlphaVar.there
            (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy045 A B R) from (by
                unfold nb089AlphaDummy045;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 0))))
            (show u ≠ (nb089AlphaDummy047 u A B R) from (by
                unfold nb089AlphaDummy047;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 0))))
            (TAlphaVar.there
              (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy077 A B R) from (by
                  unfold nb089AlphaDummy077;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0080 A B R) 0))))
              (show u ≠ (nb089AlphaDummy078 u A B R) from (by
                  unfold nb089AlphaDummy078;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb089_support_mem_0081 u A B R) 0)))) (TAlphaVar.there
                (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy049 A B R) from (by
                    unfold nb089AlphaDummy049;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb089_support_mem_0077 A B R) 0))))
                (show u ≠ (nb089AlphaDummy050 u A B R) from (by
                    unfold nb089AlphaDummy050;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb089_support_mem_0079 u A B R) 0))))
                (TAlphaVar.there
                  (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy043 A B R) from (by
                      unfold nb089AlphaDummy043;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb089_support_mem_0074 A B R) 0))))
                  (show u ≠ (nb089AlphaDummy044 u A B R) from (by
                      unfold nb089AlphaDummy044;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb089_support_mem_0075 u A B R) 0))))
                  (TAlphaVar.there
                    (show (nb089AlphaDummy000 A B R) ≠ (nb089AlphaDummy003 A B R) from (by
                        unfold nb089AlphaDummy003;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb089_support_mem_0004 A B R) 0))))
                    (show u ≠ (nb089AlphaDummy004 u A B R) from (by
                        unfold nb089AlphaDummy004;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb089_support_mem_0005 u A B R) 0))))
                    (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((synCsn (Class.cv (nb089AlphaDummy043 A B R)))).fv ∪
                ((Class.cv (nb089AlphaDummy000 A B R))).fv) (by decide)) (freshVar_injective
              (((synCsn (Class.cv (nb089AlphaDummy044 u A B R)))).fv ∪ ((Class.cv u)).fv)
              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089AlphaDummy046 A B R) ≠
                                        (nb089AlphaDummy055 A B R) from (by
                                        unfold nb089AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0052 A B R) 0)))) (show
                                      (nb089AlphaDummy048 u A B R) ≠
                                        (nb089AlphaDummy057 u A B R) from (by
                                        unfold nb089AlphaDummy057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0053 u A B R) 0))))
                                    (TAlphaVar.there (show (nb089AlphaDummy046 A B R) ≠
        (nb089AlphaDummy056 A B R) from (by
                                          unfold nb089AlphaDummy056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0052 A B R) 1)))) (show
                                        (nb089AlphaDummy048 u A B R) ≠
        (nb089AlphaDummy058 u A B R) from (by
                                          unfold nb089AlphaDummy058;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0053 u A B R) 1))))
                                      (TAlphaVar.there (show (nb089AlphaDummy046 A B R) ≠
        (nb089AlphaDummy081 A B R) from (by
          unfold nb089AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0084 A B R) 0)))) (show (nb089AlphaDummy048 u A B R) ≠
        (nb089AlphaDummy082 u A B R) from (by
          unfold nb089AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0085 u A B R) 0)))) (TAlphaVar.there (show
        (nb089AlphaDummy046 A B R) ≠ (nb089AlphaDummy079 A B R) from (by
          unfold nb089AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0082 A B R) 0)))) (show (nb089AlphaDummy048 u A B R) ≠
        (nb089AlphaDummy080 u A B R) from (by
          unfold nb089AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0083 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb089AlphaDummy046 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb089AlphaDummy048 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠ (nb089AlphaDummy062 A B R)
        from (by
          unfold nb089AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056
                    A B R)
                  1)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy065 u A B R)
        from (by
          unfold nb089AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy061 A B R) from (by
          unfold nb089AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056
                    A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy064 u A B R)
        from (by
          unfold nb089AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
          unfold
            nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054
                    A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold
            nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy063 A B R), (nb089AlphaDummy066 u A B R)),
        ((nb089AlphaDummy062 A B R), (nb089AlphaDummy065 u A B R)),
        ((nb089AlphaDummy061 A B R), (nb089AlphaDummy064 u A B R)),
        ((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy081 A B R), (nb089AlphaDummy082 u A B R)),
        ((nb089AlphaDummy079 A B R), (nb089AlphaDummy080 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy069 A B R) from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy069 A B R) from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠ (nb089AlphaDummy069 A B R)
        from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy069 A B R) from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy063 A B R), (nb089AlphaDummy066 u A B R)),
        ((nb089AlphaDummy062 A B R), (nb089AlphaDummy065 u A B R)),
        ((nb089AlphaDummy061 A B R), (nb089AlphaDummy064 u A B R)),
        ((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy081 A B R), (nb089AlphaDummy082 u A B R)),
        ((nb089AlphaDummy079 A B R), (nb089AlphaDummy080 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057
        u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠ (nb089AlphaDummy073 A B R)
        from (by
          unfold
            nb089AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy074 u A B R)
        from (by
          unfold
            nb089AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy062
        A B R) ≠ (nb089AlphaDummy073 A B R) from (by
          unfold
            nb089AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy074 u A B R)
        from (by
          unfold
            nb089AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠ (nb089AlphaDummy075 A B R)
        from (by
          unfold
            nb089AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy076 u A B R)
        from (by
          unfold
            nb089AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy075 A B R) from (by
          unfold
            nb089AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy076 u A B R)
        from (by
          unfold
            nb089AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
          unfold nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy081 A B R), (nb089AlphaDummy082 u A B R)),
        ((nb089AlphaDummy079 A B R), (nb089AlphaDummy080 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠ (nb089AlphaDummy059 A B R)
        from (by
          unfold nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
          unfold nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy081 A B R), (nb089AlphaDummy082 u A B R)),
        ((nb089AlphaDummy079 A B R), (nb089AlphaDummy080 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089AlphaDummy046 A B R) ≠
                                        (nb089AlphaDummy055 A B R) from (by
                                        unfold nb089AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0052 A B R) 0)))) (show
                                      (nb089AlphaDummy048 u A B R) ≠
                                        (nb089AlphaDummy057 u A B R) from (by
                                        unfold nb089AlphaDummy057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0053 u A B R) 0))))
                                    (TAlphaVar.there (show (nb089AlphaDummy046 A B R) ≠
        (nb089AlphaDummy056 A B R) from (by
                                          unfold nb089AlphaDummy056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0052 A B R) 1)))) (show
                                        (nb089AlphaDummy048 u A B R) ≠
        (nb089AlphaDummy058 u A B R) from (by
                                          unfold nb089AlphaDummy058;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0053 u A B R) 1))))
                                      (TAlphaVar.there (show (nb089AlphaDummy046 A B R) ≠
        (nb089AlphaDummy081 A B R) from (by
          unfold nb089AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0084 A B R) 0)))) (show (nb089AlphaDummy048 u A B R) ≠
        (nb089AlphaDummy082 u A B R) from (by
          unfold nb089AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0085 u A B R) 0)))) (TAlphaVar.there (show
        (nb089AlphaDummy046 A B R) ≠ (nb089AlphaDummy079 A B R) from (by
          unfold nb089AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0082 A B R) 0)))) (show (nb089AlphaDummy048 u A B R) ≠
        (nb089AlphaDummy080 u A B R) from (by
          unfold nb089AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0083 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb089AlphaDummy046 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb089AlphaDummy048 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠ (nb089AlphaDummy062 A B R)
        from (by
          unfold nb089AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056
                    A B R)
                  1)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy065 u A B R)
        from (by
          unfold nb089AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy061 A B R) from (by
          unfold nb089AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056
                    A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy064 u A B R)
        from (by
          unfold nb089AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
          unfold
            nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054
                    A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold
            nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy063 A B R), (nb089AlphaDummy066 u A B R)),
        ((nb089AlphaDummy062 A B R), (nb089AlphaDummy065 u A B R)),
        ((nb089AlphaDummy061 A B R), (nb089AlphaDummy064 u A B R)),
        ((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy081 A B R), (nb089AlphaDummy082 u A B R)),
        ((nb089AlphaDummy079 A B R), (nb089AlphaDummy080 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy069 A B R) from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy069 A B R) from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠ (nb089AlphaDummy069 A B R)
        from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy069 A B R) from (by
          unfold
            nb089AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy070 u A B R)
        from (by
          unfold
            nb089AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy067 A B R) from (by
          unfold
            nb089AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy068 u A B R)
        from (by
          unfold
            nb089AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy063 A B R), (nb089AlphaDummy066 u A B R)),
        ((nb089AlphaDummy062 A B R), (nb089AlphaDummy065 u A B R)),
        ((nb089AlphaDummy061 A B R), (nb089AlphaDummy064 u A B R)),
        ((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy081 A B R), (nb089AlphaDummy082 u A B R)),
        ((nb089AlphaDummy079 A B R), (nb089AlphaDummy080 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089AlphaDummy055 A B R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055 A B R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057
        u A B R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠ (nb089AlphaDummy073 A B R)
        from (by
          unfold
            nb089AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy074 u A B R)
        from (by
          unfold
            nb089AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy062
        A B R) ≠ (nb089AlphaDummy073 A B R) from (by
          unfold
            nb089AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy074 u A B R)
        from (by
          unfold
            nb089AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy062 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy065 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089AlphaDummy055
        A B R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089AlphaDummy057 u A B R))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠ (nb089AlphaDummy075 A B R)
        from (by
          unfold
            nb089AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy076 u A B R)
        from (by
          unfold
            nb089AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy063
        A B R) ≠ (nb089AlphaDummy075 A B R) from (by
          unfold
            nb089AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy076 u A B R)
        from (by
          unfold
            nb089AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089AlphaDummy063 A B R) ≠
        (nb089AlphaDummy071 A B R) from (by
          unfold
            nb089AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb089AlphaDummy066 u A B R) ≠ (nb089AlphaDummy072 u A B R)
        from (by
          unfold
            nb089AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
          unfold nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy081 A B R), (nb089AlphaDummy082 u A B R)),
        ((nb089AlphaDummy079 A B R), (nb089AlphaDummy080 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠ (nb089AlphaDummy059 A B R)
        from (by
          unfold nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089AlphaDummy055 A B R) ≠
        (nb089AlphaDummy059 A B R) from (by
          unfold nb089AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089AlphaDummy057 u A B R) ≠ (nb089AlphaDummy060 u A B R)
        from (by
          unfold nb089AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb089AlphaDummy059 A B R), (nb089AlphaDummy060 u A B R)),
        ((nb089AlphaDummy055 A B R), (nb089AlphaDummy057 u A B R)),
        ((nb089AlphaDummy056 A B R), (nb089AlphaDummy058 u A B R)),
        ((nb089AlphaDummy081 A B R), (nb089AlphaDummy082 u A B R)),
        ((nb089AlphaDummy079 A B R), (nb089AlphaDummy080 u A B R)),
        ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
        ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
        ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
        ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
        ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u), ((nb089AlphaDummy005 A B R),
        (nb089AlphaDummy006 u A B R)), ((nb089AlphaDummy001 A B R),
        (nb089AlphaDummy002 u A B R))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb089AlphaDummy079 A B R), (nb089AlphaDummy080 u A B R)),
                    ((nb089AlphaDummy046 A B R), (nb089AlphaDummy048 u A B R)),
                    ((nb089AlphaDummy045 A B R), (nb089AlphaDummy047 u A B R)),
                    ((nb089AlphaDummy077 A B R), (nb089AlphaDummy078 u A B R)),
                    ((nb089AlphaDummy049 A B R), (nb089AlphaDummy050 u A B R)),
                    ((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
                    ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
                    ((nb089AlphaDummy000 A B R), u),
                    ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
                    ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb089_focused_notmem_0007 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy043 A B R) ∉ A.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089AlphaDummy000 A B R))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb089_focused_notmem_0008 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy043 A B R) ∉ B.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089AlphaDummy000 A B R))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb089_focused_notmem_0009 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy043 A B R) ∉ R.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089AlphaDummy000 A B R))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb089_wpp_notmem_0212 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy043 A B R) ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [nb089AlphaDummy043, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0007 A B R) (nb089_focused_notmem_0008 A B R))
      (nb089_focused_notmem_0009 A B R))

theorem nb089_focused_notmem_0010 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy044 u A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb089_focused_notmem_0011 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy044 u A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb089_focused_notmem_0012 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy044 u A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb089_wpp_notmem_0213 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy044 u A B R) ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [nb089AlphaDummy044, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb089_focused_notmem_0010 u A B R) (nb089_focused_notmem_0011 u A B R))
      (nb089_focused_notmem_0012 u A B R))

theorem nb089_focused_notmem_0013 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
            ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
          ((synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_focused_notmem_0014 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb089AlphaDummy000 A B R)} : Finset Var) ∪
            ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
          ((synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0214 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy003 A B R) ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [nb089AlphaDummy003, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0000 A B R) (nb089_focused_notmem_0013 A B R))
      (nb089_focused_notmem_0014 A B R))

theorem nb089_focused_notmem_0015 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
          ((synCfdrowfib R A B (Class.cv u))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_focused_notmem_0016 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((synCpw1 (synCpw1 (synCuni A)))).fv ∪
          ((synCfdrowfib R A B (Class.cv u))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0215 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy004 u A B R) ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [nb089AlphaDummy004, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb089_focused_notmem_0001 u A B R) (nb089_focused_notmem_0015 u A B R))
      (nb089_focused_notmem_0016 u A B R))

theorem nb089_focused_notmem_0017 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb089_focused_notmem_0018 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb089_wpp_notmem_0216 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy000 A B R) ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [nb089AlphaDummy000, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0002 A B R) (nb089_focused_notmem_0017 A B R))
      (nb089_focused_notmem_0018 A B R))

theorem nb089_wpp_notmem_0217 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    u ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_u dv_B_u) dv_R_u)

theorem nb089_focused_notmem_0019 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy005 A B R) ∉ B.fv :=
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
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb089AlphaDummy000 A B R)) (synCpw1 (synCpw1 (synCuni A))))
      (Wff.classEq (Class.cv (nb089AlphaDummy003 A B R))
        (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb089AlphaDummy003 A B R))
      (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_focused_notmem_0020 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy005 A B R) ∉ R.fv :=
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
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb089AlphaDummy000 A B R)) (synCpw1 (synCpw1 (synCuni A))))
      (Wff.classEq (Class.cv (nb089AlphaDummy003 A B R))
        (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb089AlphaDummy003 A B R))
      (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0218 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy005 A B R) ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [nb089AlphaDummy005, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0003 A B R) (nb089_focused_notmem_0019 A B R))
      (nb089_focused_notmem_0020 A B R))

theorem nb089_focused_notmem_0021 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy006 u A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb089AlphaDummy004 u A B R)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
              (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
                (synCfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
      (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
        (synCfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb089AlphaDummy004 u A B R))
      (synCfdrowfib R A B (Class.cv u))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_focused_notmem_0022 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy006 u A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb089AlphaDummy004 u A B R)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
              (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
                (synCfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (synCpw1 (synCpw1 (synCuni A))))
      (Wff.classEq (Class.cv (nb089AlphaDummy004 u A B R))
        (synCfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb089AlphaDummy004 u A B R))
      (synCfdrowfib R A B (Class.cv u))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0219 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy006 u A B R) ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [nb089AlphaDummy006, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb089_focused_notmem_0004 u A B R) (nb089_focused_notmem_0021 u A B R))
      (nb089_focused_notmem_0022 u A B R))

theorem nb089_focused_notmem_0023 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy001 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((synWbr R (synCwe) A)).fv ∪
            ((synCmpt (nb089AlphaDummy000 A B R) (synCpw1 (synCpw1 (synCuni A)))
                (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))))).fv ∪
          ((synC0)).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cmpt (nb089AlphaDummy000 A B R) (synCpw1 (synCpw1 (synCuni A)))
      (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb089_focused_notmem_0017 A B R)) (h_eq ▸ hu)
  · rw [fv_syn_cfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    right
    exact hu

theorem nb089_focused_notmem_0024 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy001 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((synWbr R (synCwe) A)).fv ∪
            ((synCmpt (nb089AlphaDummy000 A B R) (synCpw1 (synCpw1 (synCuni A)))
                (synCfdrowfib R A B (Class.cv (nb089AlphaDummy000 A B R))))).fv ∪
          ((synC0)).fv)
        0 ∉
      R.fv
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
  left
  exact hu

theorem nb089_wpp_notmem_0220 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy001 A B R) ∉ ((synCfdrowrel R A B)).fv := by
  simpa only [nb089AlphaDummy001, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0005 A B R) (nb089_focused_notmem_0023 A B R))
      (nb089_focused_notmem_0024 A B R))

theorem nb089_focused_notmem_0025 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_B_u : u ∉ B.fv) : (nb089AlphaDummy002 u A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((synWbr R (synCwe) A)).fv ∪ ((synCmpt u (synCpw1 (synCpw1 (synCuni A)))
                (synCfdrowfib R A B (Class.cv u)))).fv ∪ ((synC0)).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (Class.cv u))]
  rw [Finset.mem_union]
  right
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => (dv_B_u) (h_eq ▸ hu)
  · rw [fv_syn_cfdrowfib R A B (Class.cv u)]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    right
    exact hu

theorem nb089_focused_notmem_0026 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy002 u A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((synWbr R (synCwe) A)).fv ∪ ((synCmpt u (synCpw1 (synCpw1 (synCuni A)))
                (synCfdrowfib R A B (Class.cv u)))).fv ∪ ((synC0)).fv)
        0 ∉
      R.fv
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
  left
  exact hu

theorem nb089_wpp_notmem_0221 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_B_u : u ∉ B.fv) : (nb089AlphaDummy002 u A B R) ∉ ((synCfdrowrel R A B)).fv :=
  by
  simpa only [nb089AlphaDummy002, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0006 u A B R)
        (nb089_focused_notmem_0025 u A B R dv_B_u)) (nb089_focused_notmem_0026 u A B R))

theorem nb089_compact_envfresh_0015 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    TEnvFresh
      [((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u),
        ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
        ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      ((synCfdrowrel R A B)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb089AlphaDummy043 A B R) (nb089AlphaDummy044 u A B R)
      (nb089_wpp_notmem_0212 A B R) (nb089_wpp_notmem_0213 u A B R)
      (TEnvFresh.consFresh (nb089AlphaDummy003 A B R) (nb089AlphaDummy004 u A B R)
        (nb089_wpp_notmem_0214 A B R) (nb089_wpp_notmem_0215 u A B R)
        (TEnvFresh.consFresh (nb089AlphaDummy000 A B R) u (nb089_wpp_notmem_0216 A B R)
          (nb089_wpp_notmem_0217 u A B R dv_A_u dv_B_u dv_R_u)
          (TEnvFresh.consFresh (nb089AlphaDummy005 A B R)
            (nb089AlphaDummy006 u A B R) (nb089_wpp_notmem_0218 A B R)
            (nb089_wpp_notmem_0219 u A B R) (TEnvFresh.consFresh (nb089AlphaDummy001 A B R)
              (nb089AlphaDummy002 u A B R) (nb089_wpp_notmem_0220 A B R)
              (nb089_wpp_notmem_0221 u A B R dv_B_u)
              (TEnvFresh.nil ((synCfdrowrel R A B)).fv))))))

/-- Checked nominal proof certificate identified upstream as `nb089_wpp_refl_0015`. -/
@[expose]
noncomputable def nb089WppRefl0015 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    TReflOn
      [((nb089AlphaDummy043 A B R), (nb089AlphaDummy044 u A B R)),
        ((nb089AlphaDummy003 A B R), (nb089AlphaDummy004 u A B R)),
        ((nb089AlphaDummy000 A B R), u),
        ((nb089AlphaDummy005 A B R), (nb089AlphaDummy006 u A B R)),
        ((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      ((synCfdrowrel R A B)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0015 u A B R dv_A_u dv_B_u dv_R_u)

theorem nb089_wpp_notmem_0222 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy001 A B R) ∉ ((Wff.neg (synWbr R (synCwe) A))).fv := by
  simpa only [nb089AlphaDummy001, fv_wff_neg, fv_syn_wbr, Finset.mem_union, not_or,
    fv_syn_cwe] using
    (And.intro (And.intro (nb089_focused_notmem_0024 A B R) (nb089_focused_notmem_0005 A B R))
      (nb089_compact_fv_empty_0026 A B R))

theorem nb089_wpp_notmem_0223 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy002 u A B R) ∉ ((Wff.neg (synWbr R (synCwe) A))).fv := by
  simpa only [nb089AlphaDummy002, fv_wff_neg, fv_syn_wbr, Finset.mem_union, not_or,
    fv_syn_cwe] using
    (And.intro
      (And.intro (nb089_focused_notmem_0026 u A B R) (nb089_focused_notmem_0006 u A B R))
      (nb089_compact_fv_empty_0027 u A B R))

theorem nb089_compact_envfresh_0016 (u : Var) (A : Class) (B : Class) (R : Class) :
    TEnvFresh [((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      ((Wff.neg (synWbr R (synCwe) A))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb089AlphaDummy001 A B R) (nb089AlphaDummy002 u A B R)
      (nb089_wpp_notmem_0222 A B R) (nb089_wpp_notmem_0223 u A B R)
      (TEnvFresh.nil ((Wff.neg (synWbr R (synCwe) A))).fv))

/-- Checked nominal proof certificate identified upstream as `nb089_wpp_refl_0016`. -/
@[expose]
noncomputable def nb089WppRefl0016 (u : Var) (A : Class) (B : Class) (R : Class) :
    TReflOn [((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      ((Wff.neg (synWbr R (synCwe) A))).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0016 u A B R)

theorem nb089_wpp_notmem_0224 (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy001 A B R) ∉ ((Wff.neg (Wff.neg (synWbr R (synCwe) A)))).fv := by
  simpa only [nb089AlphaDummy001, fv_wff_neg, fv_syn_wbr, Finset.mem_union, not_or,
    fv_syn_cwe] using
    (And.intro (And.intro (nb089_focused_notmem_0024 A B R) (nb089_focused_notmem_0005 A B R))
      (nb089_compact_fv_empty_0026 A B R))

theorem nb089_wpp_notmem_0225 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089AlphaDummy002 u A B R) ∉ ((Wff.neg (Wff.neg (synWbr R (synCwe) A)))).fv :=
  by
  simpa only [nb089AlphaDummy002, fv_wff_neg, fv_syn_wbr, Finset.mem_union, not_or,
    fv_syn_cwe] using
    (And.intro
      (And.intro (nb089_focused_notmem_0026 u A B R) (nb089_focused_notmem_0006 u A B R))
      (nb089_compact_fv_empty_0027 u A B R))

theorem nb089_compact_envfresh_0018 (u : Var) (A : Class) (B : Class) (R : Class) :
    TEnvFresh [((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      ((Wff.neg (Wff.neg (synWbr R (synCwe) A)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb089AlphaDummy001 A B R) (nb089AlphaDummy002 u A B R)
      (nb089_wpp_notmem_0224 A B R) (nb089_wpp_notmem_0225 u A B R)
      (TEnvFresh.nil ((Wff.neg (Wff.neg (synWbr R (synCwe) A)))).fv))

/-- Checked nominal proof certificate identified upstream as `nb089_wpp_refl_0018`. -/
@[expose]
noncomputable def nb089WppRefl0018 (u : Var) (A : Class) (B : Class) (R : Class) :
    TReflOn [((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
      ((Wff.neg (Wff.neg (synWbr R (synCwe) A)))).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0018 u A B R)

/-- Checked nominal proof certificate identified upstream as `nominal_df_fdglobalrowmap`. -/
@[expose]
noncomputable def nominalDfFdglobalrowmap (u : Var) (A : Class) (B : Class) (R : Class)
    (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_R : Disjoint A.fv R.fv) (dv_A_u : u ∉ A.fv)
    (__dv_B_R : Disjoint B.fv R.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    Nominal.NPrf
      (.classEq (synCfdglobalrowmap R A B) (synCif (synWbr R (synCwe) A)
          (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
          (synC0))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                    (nb089AlphaDummy003 A B R) ≠
                                      (nb089AlphaDummy005 A B R) from (by
                                      unfold nb089AlphaDummy005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0002 A B R) 0))))) (Ne.symm
                                  (show (nb089AlphaDummy004 u A B R) ≠
                                      (nb089AlphaDummy006 u A B R) from (by
                                      unfold nb089AlphaDummy006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0003 u A B R) 0)))))
                                (TAlphaVar.there (Ne.symm (show (nb089AlphaDummy000 A B R) ≠
                                        (nb089AlphaDummy005 A B R) from (by
                                        unfold nb089AlphaDummy005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0000 A B R) 0))))) (Ne.symm
                                    (show u ≠ (nb089AlphaDummy006 u A B R) from (by
                                        unfold nb089AlphaDummy006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0001 u A B R) 0)))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb089SplitAlpha0001 u A B R)))))
                          (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb089AlphaDummy000 A B R) ≠
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
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfReflOn
                                [((nb089AlphaDummy003 A B R),
                                    (nb089AlphaDummy004 u A B R)),
                                  ((nb089AlphaDummy000 A B R), u),
                                  ((nb089AlphaDummy005 A B R),
                                    (nb089AlphaDummy006 u A B R)),
                                  ((nb089AlphaDummy001 A B R),
                                    (nb089AlphaDummy002 u A B R))]
                                (synCpw1 (synCpw1 (synCuni A)))
                                (nb089WppRefl0007 u A B R dv_A_u)))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb089SplitAlpha0002 u A B R))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb089SplitAlpha0003 u A B R))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb089SplitAlpha0003 u A B R)))))))))))) (TAlphaClass.reflOfReflOn
                                    [((nb089AlphaDummy043 A B R),
                                        (nb089AlphaDummy044 u A B R)),
                                      ((nb089AlphaDummy003 A B R),
                                        (nb089AlphaDummy004 u A B R)),
                                      ((nb089AlphaDummy000 A B R), u),
                                      ((nb089AlphaDummy005 A B R),
                                        (nb089AlphaDummy006 u A B R)),
                                      ((nb089AlphaDummy001 A B R),
                                        (nb089AlphaDummy002 u A B R))] (synCfdrowrel R A B)
                                    (nb089WppRefl0015 u A B R dv_A_u dv_B_u dv_R_u)))))))))))
                (TAlphaWff.reflOfReflOn
                  [((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
                  (Wff.neg (synWbr R (synCwe) A)) (nb089WppRefl0016 u A B R)))))
          (TAlphaWff.neg (TAlphaWff.imp
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
                  (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.reflOfReflOn
                [((nb089AlphaDummy001 A B R), (nb089AlphaDummy002 u A B R))]
                (Wff.neg (Wff.neg (synWbr R (synCwe) A))) (nb089WppRefl0018 u A B R))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
