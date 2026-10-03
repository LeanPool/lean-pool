/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C084C001Part004Stage1


/-! NF weak partition development: NAR4C084C001Part004. -/


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

@[expose]
noncomputable def nb084_focused_refl_0005 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_R_d : d ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TReflOn
      [((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)]
      R.fv :=
  TEnvFresh.reflOn (nb084_compact_envfresh_0012 x y A B R d dv_R_d dv_R_x dv_R_y)

@[expose]
noncomputable def nominal_df_fdif (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (d : Var) (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_R : Disjoint A.fv R.fv)
    (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (__dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_R_d : d ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_d_x : d ≠ x) (dv_d_y : d ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cfdif R A B) (syn_crab d A (syn_wrex x B
            (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.refl_of_reflOn [((nb084_alpha_dummy_000 A B R), d)] A
              (nb084_focused_refl_0000 A B R d dv_A_d))) (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_reflOn
                  [((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)]
                  B (nb084_focused_refl_0001 x A B R d dv_B_d dv_B_x))) (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.refl_of_reflOn [((nb084_alpha_dummy_002 A B R), y),
                        ((nb084_alpha_dummy_001 A B R), x), ((nb084_alpha_dummy_000 A B R), d)]
                      B (nb084_focused_refl_0002 x y A B R d dv_B_d dv_B_x dv_B_y)))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv) (by decide)) dv_d_y
                        (TAlphaVar.there
                          (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv) (by decide))
                          dv_d_x (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_reflOn [((nb084_alpha_dummy_003 A B R),
                                (nb084_alpha_dummy_005 x y A R)),
                              ((nb084_alpha_dummy_002 A B R), y),
                              ((nb084_alpha_dummy_001 A B R), x),
                              ((nb084_alpha_dummy_000 A B R), d)]
                            A (nb084_focused_refl_0003 x y A B R d dv_A_d dv_A_x dv_A_y)))
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb084_alpha_dummy_001 A B R) ≠ (nb084_alpha_dummy_007 A B R) from (by
          unfold nb084_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0002 A B R) 0))))
        (show x ≠ (nb084_alpha_dummy_008 x y) from (by
          unfold nb084_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0003 x y) 0)))) (TAlphaVar.there (show
        (nb084_alpha_dummy_001 A B R) ≠ (nb084_alpha_dummy_003 A B R) from (by
          unfold nb084_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0000 A B R)
                  0)))) (show x ≠ (nb084_alpha_dummy_005 x y A R) from (by
          unfold nb084_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0001 x y A R)
                  0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (A).fv ∪ (B).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb084_alpha_dummy_002 A B R) ≠ (nb084_alpha_dummy_007 A B R) from (by
          unfold nb084_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0006 A B R)
                  0)))) (show y ≠ (nb084_alpha_dummy_008 x y) from (by
          unfold nb084_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb084_alpha_dummy_002 A B R) ≠ (nb084_alpha_dummy_003 A B R) from (by
          unfold nb084_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0004 A B R)
                  0)))) (show y ≠ (nb084_alpha_dummy_005 x y A R) from (by
          unfold nb084_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0005 x y A R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cv (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb084_alpha_dummy_002 A B R) ≠
        (nb084_alpha_dummy_007 A B R) from (by
          unfold nb084_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0006 A B R) 0))))
                                        (show y ≠ (nb084_alpha_dummy_008 x y) from (by
          unfold nb084_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb084_alpha_dummy_002 A B R) ≠ (nb084_alpha_dummy_003 A B R) from (by
          unfold nb084_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0004 A B R) 0))))
        (show y ≠ (nb084_alpha_dummy_005 x y A R) from (by
          unfold nb084_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0005 x y A R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cv (TAlphaVar.here _ _ _)))
                                  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb084_alpha_dummy_001 A B R) ≠
        (nb084_alpha_dummy_007 A B R) from (by
          unfold nb084_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0002 A B R) 0))))
        (show x ≠ (nb084_alpha_dummy_008 x y) from (by
          unfold nb084_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0003 x y) 0)))) (TAlphaVar.there (show
        (nb084_alpha_dummy_001 A B R) ≠ (nb084_alpha_dummy_003 A B R) from (by
          unfold nb084_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0000 A B R)
                  0)))) (show x ≠ (nb084_alpha_dummy_005 x y A R) from (by
          unfold nb084_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0001 x y A R)
                  0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (A).fv ∪ (B).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.all (TAlphaWff.imp
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_reflOn [((nb084_alpha_dummy_004 A B R),
                                      (nb084_alpha_dummy_006 x y A R)),
                                    ((nb084_alpha_dummy_003 A B R),
                                      (nb084_alpha_dummy_005 x y A R)),
                                    ((nb084_alpha_dummy_002 A B R), y),
                                    ((nb084_alpha_dummy_001 A B R), x),
                                    ((nb084_alpha_dummy_000 A B R), d)] A
                                  (nb084_focused_refl_0004 x y A B R d dv_A_d dv_A_x dv_A_y)))
                              (TAlphaWff.imp (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb084_alpha_dummy_001 A B R) ≠ (nb084_alpha_dummy_007 A B R) from (by
          unfold nb084_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0002 A B R)
                  0)))) (show x ≠ (nb084_alpha_dummy_008 x y) from (by
          unfold nb084_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0003 x y)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_001 A B R) ≠
        (nb084_alpha_dummy_004 A B R) from (by
          unfold nb084_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0000 A B
                    R)
                  1)))) (show x ≠ (nb084_alpha_dummy_006 x y A R) from (by
          unfold nb084_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0001 x y
                    A R)
                  1)))) (TAlphaVar.there (show (nb084_alpha_dummy_001 A B R) ≠
        (nb084_alpha_dummy_003 A B R) from (by
          unfold nb084_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0000 A
                    B R)
                  0)))) (show x ≠ (nb084_alpha_dummy_005 x y A R) from (by
          unfold nb084_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0001 x
                    y A R)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv)
        (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))) (TAlphaClass.cv (TAlphaVar.here _ _ _)))
        (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb084_alpha_dummy_002 A B R) ≠ (nb084_alpha_dummy_007 A B R) from (by
          unfold nb084_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0006 A B
                    R)
                  0)))) (show y ≠ (nb084_alpha_dummy_008 x y) from (by
          unfold nb084_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0007 x y)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_002 A B R) ≠
        (nb084_alpha_dummy_004 A B R) from (by
          unfold nb084_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0004 A
                    B R)
                  1)))) (show y ≠ (nb084_alpha_dummy_006 x y A R) from (by
          unfold nb084_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0005 x
                    y A R)
                  1)))) (TAlphaVar.there (show (nb084_alpha_dummy_002 A B R) ≠
        (nb084_alpha_dummy_003 A B R) from (by
          unfold nb084_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0004
                    A B R)
                  0)))) (show y ≠ (nb084_alpha_dummy_005 x y A R) from (by
          unfold nb084_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0005
                    x y A R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaClass.cv (TAlphaVar.here _ _ _))))))
                                      (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_002 A B R) ≠ (nb084_alpha_dummy_007 A B R)
        from (by
          unfold nb084_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0006 A B R)
                  0)))) (show y ≠ (nb084_alpha_dummy_008 x y) from (by
          unfold nb084_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0007 x y)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_002 A B R) ≠
        (nb084_alpha_dummy_004 A B R) from (by
          unfold nb084_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0004 A B R)
                  1)))) (show y ≠ (nb084_alpha_dummy_006 x y A R) from (by
          unfold nb084_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0005 x y A
                    R)
                  1)))) (TAlphaVar.there (show (nb084_alpha_dummy_002 A B R) ≠
        (nb084_alpha_dummy_003 A B R) from (by
          unfold nb084_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0004 A B
                    R)
                  0)))) (show y ≠ (nb084_alpha_dummy_005 x y A R) from (by
          unfold nb084_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0005 x y
                    A R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaClass.cv (TAlphaVar.here _ _ _)))
                                        (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_001 A B R) ≠ (nb084_alpha_dummy_007 A B R)
        from (by
          unfold nb084_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0002 A B R)
                  0)))) (show x ≠ (nb084_alpha_dummy_008 x y) from (by
          unfold nb084_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0003 x y)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_001 A B R) ≠
        (nb084_alpha_dummy_004 A B R) from (by
          unfold nb084_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0000 A B
                    R)
                  1)))) (show x ≠ (nb084_alpha_dummy_006 x y A R) from (by
          unfold nb084_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0001 x y
                    A R)
                  1)))) (TAlphaVar.there (show (nb084_alpha_dummy_001 A B R) ≠
        (nb084_alpha_dummy_003 A B R) from (by
          unfold nb084_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0000 A
                    B R)
                  0)))) (show x ≠ (nb084_alpha_dummy_005 x y A R) from (by
          unfold nb084_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0001 x
                    y A R)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv)
        (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))
        (TAlphaClass.cv (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb084_split_alpha_0000 x y A B R d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb084_split_alpha_0001 x y A B R d)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb084_split_alpha_0001 x y A B R d))))))))))))
                                  (TAlphaClass.refl_of_reflOn [((nb084_alpha_dummy_004 A B R),
                                        (nb084_alpha_dummy_006 x y A R)),
                                      ((nb084_alpha_dummy_003 A B R),
                                        (nb084_alpha_dummy_005 x y A R)),
                                      ((nb084_alpha_dummy_002 A B R), y),
                                      ((nb084_alpha_dummy_001 A B R), x),
                                      ((nb084_alpha_dummy_000 A B R), d)] R
                                    (nb084_focused_refl_0005 x y A B R d dv_R_d dv_R_x
                                      dv_R_y))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
