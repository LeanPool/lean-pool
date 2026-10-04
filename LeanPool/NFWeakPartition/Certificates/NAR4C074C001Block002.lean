/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C074C001Part006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C074C001Part008`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb074_split_alpha_0003`. -/
@[expose]
noncomputable def nb074SplitAlpha0003 (x : Var) :
    TAlphaWff
      [((nb074AlphaDummy046), (nb074AlphaDummy048 x)),
        ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
        ((nb074AlphaDummy075), (nb074AlphaDummy076 x)),
        ((nb074AlphaDummy049), (nb074AlphaDummy050 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy046))
          (Class.cv (nb074AlphaDummy041))) (Wff.neg
          (Wff.classEq (Class.cv (nb074AlphaDummy045))
            (synCun (synCphi (Class.cv (nb074AlphaDummy046))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy048 x))
          (Class.cv (nb074AlphaDummy043 x))) (Wff.neg
          (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
            (synCun (synCphi (Class.cv (nb074AlphaDummy048 x))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy041) ≠ (nb074AlphaDummy046) from (by
              unfold nb074AlphaDummy046;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 1))))
          (show (nb074AlphaDummy043 x) ≠ (nb074AlphaDummy048 x) from (by
              unfold nb074AlphaDummy048;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 1))))
          (TAlphaVar.there (show (nb074AlphaDummy041) ≠ (nb074AlphaDummy045) from (by
                unfold nb074AlphaDummy045;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 0))))
            (show (nb074AlphaDummy043 x) ≠ (nb074AlphaDummy047 x) from (by
                unfold nb074AlphaDummy047;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 0))))
            (TAlphaVar.there (show (nb074AlphaDummy041) ≠ (nb074AlphaDummy075) from (by
                  unfold nb074AlphaDummy075;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0076) 0))))
              (show (nb074AlphaDummy043 x) ≠ (nb074AlphaDummy076 x) from (by
                  unfold nb074AlphaDummy076;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0077 x) 0))))
              (TAlphaVar.there (show (nb074AlphaDummy041) ≠ (nb074AlphaDummy049) from (by
                    unfold nb074AlphaDummy049;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0073) 0))))
                (show (nb074AlphaDummy043 x) ≠ (nb074AlphaDummy050 x) from (by
                    unfold nb074AlphaDummy050;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0075 x) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((synCcnv (Class.cv (nb074AlphaDummy000)))).fv ∪ ((synCvv)).fv)
                    (by decide))
                  (freshVar_injective (((synCcnv (Class.cv x))).fv ∪ ((synCvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb074AlphaDummy042))).fv ∪
                ((Class.cv (nb074AlphaDummy041))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb074AlphaDummy044 x))).fv ∪
                ((Class.cv (nb074AlphaDummy043 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy046) ≠ (nb074AlphaDummy053) from (by
                                        unfold nb074AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0050)
                                                0)))) (show (nb074AlphaDummy048 x) ≠
                                        (nb074AlphaDummy055 x) from (by
                                        unfold nb074AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0051 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb074AlphaDummy046) ≠ (nb074AlphaDummy054) from
                                        (by
                                          unfold nb074AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0050)
                                                  1)))) (show (nb074AlphaDummy048 x) ≠
        (nb074AlphaDummy056 x) from (by
                                          unfold nb074AlphaDummy056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0051 x) 1))))
                                      (TAlphaVar.there (show (nb074AlphaDummy046) ≠
        (nb074AlphaDummy079) from (by
          unfold nb074AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0080) 0)))) (show (nb074AlphaDummy048 x) ≠
        (nb074AlphaDummy080 x) from (by
          unfold nb074AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0081 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy046) ≠ (nb074AlphaDummy077) from (by
          unfold nb074AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0078) 0)))) (show (nb074AlphaDummy048 x) ≠
        (nb074AlphaDummy078 x) from (by
          unfold nb074AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0079 x) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb074AlphaDummy046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb074AlphaDummy048 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy060) from (by
          unfold nb074AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  1)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy063 x) from (by
          unfold nb074AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy059)
        from (by
          unfold nb074AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  0)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy062 x) from (by
          unfold nb074AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057)
        from (by
          unfold
            nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052)
                  0)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy058 x) from (by
          unfold
            nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy061), (nb074AlphaDummy064 x)), ((nb074AlphaDummy060),
        (nb074AlphaDummy063 x)), ((nb074AlphaDummy059), (nb074AlphaDummy062 x)),
        ((nb074AlphaDummy057), (nb074AlphaDummy058 x)), ((nb074AlphaDummy053),
        (nb074AlphaDummy055 x)), ((nb074AlphaDummy054), (nb074AlphaDummy056 x)),
        ((nb074AlphaDummy079), (nb074AlphaDummy080 x)), ((nb074AlphaDummy077),
        (nb074AlphaDummy078 x)), ((nb074AlphaDummy046), (nb074AlphaDummy048 x)),
        ((nb074AlphaDummy045), (nb074AlphaDummy047 x)), ((nb074AlphaDummy075),
        (nb074AlphaDummy076 x)), ((nb074AlphaDummy049), (nb074AlphaDummy050 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy061), (nb074AlphaDummy064 x)), ((nb074AlphaDummy060),
        (nb074AlphaDummy063 x)), ((nb074AlphaDummy059), (nb074AlphaDummy062 x)),
        ((nb074AlphaDummy057), (nb074AlphaDummy058 x)), ((nb074AlphaDummy053),
        (nb074AlphaDummy055 x)), ((nb074AlphaDummy054), (nb074AlphaDummy056 x)),
        ((nb074AlphaDummy079), (nb074AlphaDummy080 x)), ((nb074AlphaDummy077),
        (nb074AlphaDummy078 x)), ((nb074AlphaDummy046), (nb074AlphaDummy048 x)),
        ((nb074AlphaDummy045), (nb074AlphaDummy047 x)), ((nb074AlphaDummy075),
        (nb074AlphaDummy076 x)), ((nb074AlphaDummy049), (nb074AlphaDummy050 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy053))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy060) ≠
        (nb074AlphaDummy071) from (by
          unfold
            nb074AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy072 x) from (by
          unfold
            nb074AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy060) ≠
        (nb074AlphaDummy071) from (by
          unfold
            nb074AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy072 x) from (by
          unfold
            nb074AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy073) from (by
          unfold
            nb074AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy074 x) from (by
          unfold
            nb074AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy073) from (by
          unfold
            nb074AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy074 x) from (by
          unfold
            nb074AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057)
        from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb074AlphaDummy057), (nb074AlphaDummy058 x)),
        ((nb074AlphaDummy053), (nb074AlphaDummy055 x)), ((nb074AlphaDummy054),
        (nb074AlphaDummy056 x)), ((nb074AlphaDummy079), (nb074AlphaDummy080 x)),
        ((nb074AlphaDummy077), (nb074AlphaDummy078 x)), ((nb074AlphaDummy046),
        (nb074AlphaDummy048 x)), ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
        ((nb074AlphaDummy075), (nb074AlphaDummy076 x)), ((nb074AlphaDummy049),
        (nb074AlphaDummy050 x)), ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb074AlphaDummy057), (nb074AlphaDummy058 x)),
        ((nb074AlphaDummy053), (nb074AlphaDummy055 x)), ((nb074AlphaDummy054),
        (nb074AlphaDummy056 x)), ((nb074AlphaDummy079), (nb074AlphaDummy080 x)),
        ((nb074AlphaDummy077), (nb074AlphaDummy078 x)), ((nb074AlphaDummy046),
        (nb074AlphaDummy048 x)), ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
        ((nb074AlphaDummy075), (nb074AlphaDummy076 x)), ((nb074AlphaDummy049),
        (nb074AlphaDummy050 x)), ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy046) ≠ (nb074AlphaDummy053) from (by
                                        unfold nb074AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0050)
                                                0)))) (show (nb074AlphaDummy048 x) ≠
                                        (nb074AlphaDummy055 x) from (by
                                        unfold nb074AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0051 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb074AlphaDummy046) ≠ (nb074AlphaDummy054) from
                                        (by
                                          unfold nb074AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0050)
                                                  1)))) (show (nb074AlphaDummy048 x) ≠
        (nb074AlphaDummy056 x) from (by
                                          unfold nb074AlphaDummy056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0051 x) 1))))
                                      (TAlphaVar.there (show (nb074AlphaDummy046) ≠
        (nb074AlphaDummy079) from (by
          unfold nb074AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0080) 0)))) (show (nb074AlphaDummy048 x) ≠
        (nb074AlphaDummy080 x) from (by
          unfold nb074AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0081 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy046) ≠ (nb074AlphaDummy077) from (by
          unfold nb074AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0078) 0)))) (show (nb074AlphaDummy048 x) ≠
        (nb074AlphaDummy078 x) from (by
          unfold nb074AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0079 x) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb074AlphaDummy046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb074AlphaDummy048 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy060) from (by
          unfold nb074AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  1)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy063 x) from (by
          unfold nb074AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy059)
        from (by
          unfold nb074AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  0)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy062 x) from (by
          unfold nb074AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057)
        from (by
          unfold
            nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052)
                  0)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy058 x) from (by
          unfold
            nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy061), (nb074AlphaDummy064 x)), ((nb074AlphaDummy060),
        (nb074AlphaDummy063 x)), ((nb074AlphaDummy059), (nb074AlphaDummy062 x)),
        ((nb074AlphaDummy057), (nb074AlphaDummy058 x)), ((nb074AlphaDummy053),
        (nb074AlphaDummy055 x)), ((nb074AlphaDummy054), (nb074AlphaDummy056 x)),
        ((nb074AlphaDummy079), (nb074AlphaDummy080 x)), ((nb074AlphaDummy077),
        (nb074AlphaDummy078 x)), ((nb074AlphaDummy046), (nb074AlphaDummy048 x)),
        ((nb074AlphaDummy045), (nb074AlphaDummy047 x)), ((nb074AlphaDummy075),
        (nb074AlphaDummy076 x)), ((nb074AlphaDummy049), (nb074AlphaDummy050 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy061), (nb074AlphaDummy064 x)), ((nb074AlphaDummy060),
        (nb074AlphaDummy063 x)), ((nb074AlphaDummy059), (nb074AlphaDummy062 x)),
        ((nb074AlphaDummy057), (nb074AlphaDummy058 x)), ((nb074AlphaDummy053),
        (nb074AlphaDummy055 x)), ((nb074AlphaDummy054), (nb074AlphaDummy056 x)),
        ((nb074AlphaDummy079), (nb074AlphaDummy080 x)), ((nb074AlphaDummy077),
        (nb074AlphaDummy078 x)), ((nb074AlphaDummy046), (nb074AlphaDummy048 x)),
        ((nb074AlphaDummy045), (nb074AlphaDummy047 x)), ((nb074AlphaDummy075),
        (nb074AlphaDummy076 x)), ((nb074AlphaDummy049), (nb074AlphaDummy050 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy053))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy060) ≠
        (nb074AlphaDummy071) from (by
          unfold
            nb074AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy072 x) from (by
          unfold
            nb074AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy060) ≠
        (nb074AlphaDummy071) from (by
          unfold
            nb074AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy072 x) from (by
          unfold
            nb074AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy073) from (by
          unfold
            nb074AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy074 x) from (by
          unfold
            nb074AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy073) from (by
          unfold
            nb074AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy074 x) from (by
          unfold
            nb074AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057)
        from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb074AlphaDummy057), (nb074AlphaDummy058 x)),
        ((nb074AlphaDummy053), (nb074AlphaDummy055 x)), ((nb074AlphaDummy054),
        (nb074AlphaDummy056 x)), ((nb074AlphaDummy079), (nb074AlphaDummy080 x)),
        ((nb074AlphaDummy077), (nb074AlphaDummy078 x)), ((nb074AlphaDummy046),
        (nb074AlphaDummy048 x)), ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
        ((nb074AlphaDummy075), (nb074AlphaDummy076 x)), ((nb074AlphaDummy049),
        (nb074AlphaDummy050 x)), ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb074AlphaDummy057), (nb074AlphaDummy058 x)),
        ((nb074AlphaDummy053), (nb074AlphaDummy055 x)), ((nb074AlphaDummy054),
        (nb074AlphaDummy056 x)), ((nb074AlphaDummy079), (nb074AlphaDummy080 x)),
        ((nb074AlphaDummy077), (nb074AlphaDummy078 x)), ((nb074AlphaDummy046),
        (nb074AlphaDummy048 x)), ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
        ((nb074AlphaDummy075), (nb074AlphaDummy076 x)), ((nb074AlphaDummy049),
        (nb074AlphaDummy050 x)), ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb074AlphaDummy077), (nb074AlphaDummy078 x)),
                    ((nb074AlphaDummy046), (nb074AlphaDummy048 x)),
                    ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
                    ((nb074AlphaDummy075), (nb074AlphaDummy076 x)),
                    ((nb074AlphaDummy049), (nb074AlphaDummy050 x)),
                    ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                    ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                    ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                    ((nb074AlphaDummy000), x),
                    ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb074_split_alpha_0004`. -/
@[expose]
noncomputable def nb074SplitAlpha0004 (x : Var) :
    TAlphaWff
      [((nb074AlphaDummy049), (nb074AlphaDummy050 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy049)) (synCcompl
            (Class.cab (nb074AlphaDummy045)
              (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy042))
                (Wff.classEq (Class.cv (nb074AlphaDummy045))
                  (synCphi (Class.cv (nb074AlphaDummy046)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy049)) (synCcompl
              (Class.cab (nb074AlphaDummy045)
                (synWrex (nb074AlphaDummy046) (Class.cv (nb074AlphaDummy041))
                  (Wff.classEq (Class.cv (nb074AlphaDummy045))
                    (synCun (synCphi (Class.cv (nb074AlphaDummy046)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy050 x)) (synCcompl
            (Class.cab (nb074AlphaDummy047 x)
              (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy044 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                  (synCphi (Class.cv (nb074AlphaDummy048 x)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy050 x)) (synCcompl
              (Class.cab (nb074AlphaDummy047 x)
                (synWrex (nb074AlphaDummy048 x) (Class.cv (nb074AlphaDummy043 x))
                  (Wff.classEq (Class.cv (nb074AlphaDummy047 x))
                    (synCun (synCphi (Class.cv (nb074AlphaDummy048 x)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy046) from (by
                              unfold nb074AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0044) 1))))
                          (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy048 x) from (by
                              unfold nb074AlphaDummy048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0046 x) 1))))
                          (TAlphaVar.there
                            (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy045) from (by
                                unfold nb074AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0044) 0))))
                            (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy047 x) from (by
                                unfold nb074AlphaDummy047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0046 x) 0))))
                            (TAlphaVar.there
                              (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy051) from (by
                                  unfold nb074AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0048) 0))))
                              (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy052 x) from
                                (by
                                  unfold nb074AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy049) from (by
                                    unfold nb074AlphaDummy049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0045) 0)))) (show
                                  (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy050 x) from (by
                                    unfold nb074AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0047 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb074AlphaDummy042))).fv ∪
                              ((Class.cv (nb074AlphaDummy041))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb074AlphaDummy044 x))).fv ∪
                              ((Class.cv (nb074AlphaDummy043 x))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074AlphaDummy046) ≠ (nb074AlphaDummy053) from
                                    (by
                                      unfold nb074AlphaDummy053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0050)
                                              0)))) (show
                                    (nb074AlphaDummy048 x) ≠ (nb074AlphaDummy055 x) from
                                    (by
                                      unfold nb074AlphaDummy055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0051 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb074AlphaDummy046) ≠ (nb074AlphaDummy054) from (by
                                        unfold nb074AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0050)
                                                1)))) (show (nb074AlphaDummy048 x) ≠
                                        (nb074AlphaDummy056 x) from (by
                                        unfold nb074AlphaDummy056;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0051 x)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb074AlphaDummy046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb074AlphaDummy048 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy053) ≠ (nb074AlphaDummy060) from (by
          unfold nb074AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  1)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy063 x) from (by
          unfold nb074AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055 x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy059)
        from (by
          unfold nb074AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  0)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy062 x) from (by
          unfold nb074AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057)
        from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052)
                  0)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy061), (nb074AlphaDummy064 x)), ((nb074AlphaDummy060),
        (nb074AlphaDummy063 x)), ((nb074AlphaDummy059), (nb074AlphaDummy062 x)),
        ((nb074AlphaDummy057), (nb074AlphaDummy058 x)), ((nb074AlphaDummy053),
        (nb074AlphaDummy055 x)), ((nb074AlphaDummy054), (nb074AlphaDummy056 x)),
        ((nb074AlphaDummy046), (nb074AlphaDummy048 x)), ((nb074AlphaDummy045),
        (nb074AlphaDummy047 x)), ((nb074AlphaDummy051), (nb074AlphaDummy052 x)),
        ((nb074AlphaDummy049), (nb074AlphaDummy050 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy061), (nb074AlphaDummy064 x)), ((nb074AlphaDummy060),
        (nb074AlphaDummy063 x)), ((nb074AlphaDummy059), (nb074AlphaDummy062 x)),
        ((nb074AlphaDummy057), (nb074AlphaDummy058 x)), ((nb074AlphaDummy053),
        (nb074AlphaDummy055 x)), ((nb074AlphaDummy054), (nb074AlphaDummy056 x)),
        ((nb074AlphaDummy046), (nb074AlphaDummy048 x)), ((nb074AlphaDummy045),
        (nb074AlphaDummy047 x)), ((nb074AlphaDummy051), (nb074AlphaDummy052 x)),
        ((nb074AlphaDummy049), (nb074AlphaDummy050 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy060) ≠
        (nb074AlphaDummy071) from (by
          unfold
            nb074AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy072 x) from (by
          unfold
            nb074AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy060) ≠
        (nb074AlphaDummy071) from (by
          unfold
            nb074AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy072 x) from (by
          unfold
            nb074AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy073) from (by
          unfold
            nb074AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy074 x) from (by
          unfold
            nb074AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy073) from (by
          unfold
            nb074AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy074 x) from (by
          unfold
            nb074AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb074AlphaDummy057),
        (nb074AlphaDummy058 x)), ((nb074AlphaDummy053), (nb074AlphaDummy055 x)),
        ((nb074AlphaDummy054), (nb074AlphaDummy056 x)), ((nb074AlphaDummy046),
        (nb074AlphaDummy048 x)), ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
        ((nb074AlphaDummy051), (nb074AlphaDummy052 x)), ((nb074AlphaDummy049),
        (nb074AlphaDummy050 x)), ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb074AlphaDummy057),
        (nb074AlphaDummy058 x)), ((nb074AlphaDummy053), (nb074AlphaDummy055 x)),
        ((nb074AlphaDummy054), (nb074AlphaDummy056 x)), ((nb074AlphaDummy046),
        (nb074AlphaDummy048 x)), ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
        ((nb074AlphaDummy051), (nb074AlphaDummy052 x)), ((nb074AlphaDummy049),
        (nb074AlphaDummy050 x)), ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy046) from (by
                              unfold nb074AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0044) 1))))
                          (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy048 x) from (by
                              unfold nb074AlphaDummy048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0046 x) 1))))
                          (TAlphaVar.there
                            (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy045) from (by
                                unfold nb074AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0044) 0))))
                            (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy047 x) from (by
                                unfold nb074AlphaDummy047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0046 x) 0))))
                            (TAlphaVar.there
                              (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy051) from (by
                                  unfold nb074AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0048) 0))))
                              (show (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy052 x) from
                                (by
                                  unfold nb074AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb074AlphaDummy042) ≠ (nb074AlphaDummy049) from (by
                                    unfold nb074AlphaDummy049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0045) 0)))) (show
                                  (nb074AlphaDummy044 x) ≠ (nb074AlphaDummy050 x) from (by
                                    unfold nb074AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0047 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb074AlphaDummy042))).fv ∪
                              ((Class.cv (nb074AlphaDummy041))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb074AlphaDummy044 x))).fv ∪
                              ((Class.cv (nb074AlphaDummy043 x))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074AlphaDummy046) ≠ (nb074AlphaDummy053) from
                                    (by
                                      unfold nb074AlphaDummy053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0050)
                                              0)))) (show
                                    (nb074AlphaDummy048 x) ≠ (nb074AlphaDummy055 x) from
                                    (by
                                      unfold nb074AlphaDummy055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0051 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb074AlphaDummy046) ≠ (nb074AlphaDummy054) from (by
                                        unfold nb074AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0050)
                                                1)))) (show (nb074AlphaDummy048 x) ≠
                                        (nb074AlphaDummy056 x) from (by
                                        unfold nb074AlphaDummy056;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0051 x)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb074AlphaDummy046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb074AlphaDummy048 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy053) ≠ (nb074AlphaDummy060) from (by
          unfold nb074AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  1)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy063 x) from (by
          unfold nb074AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055 x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy059)
        from (by
          unfold nb074AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0054)
                  0)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy062 x) from (by
          unfold nb074AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy053) ≠ (nb074AlphaDummy057)
        from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052)
                  0)))) (show (nb074AlphaDummy055 x) ≠ (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy061), (nb074AlphaDummy064 x)), ((nb074AlphaDummy060),
        (nb074AlphaDummy063 x)), ((nb074AlphaDummy059), (nb074AlphaDummy062 x)),
        ((nb074AlphaDummy057), (nb074AlphaDummy058 x)), ((nb074AlphaDummy053),
        (nb074AlphaDummy055 x)), ((nb074AlphaDummy054), (nb074AlphaDummy056 x)),
        ((nb074AlphaDummy046), (nb074AlphaDummy048 x)), ((nb074AlphaDummy045),
        (nb074AlphaDummy047 x)), ((nb074AlphaDummy051), (nb074AlphaDummy052 x)),
        ((nb074AlphaDummy049), (nb074AlphaDummy050 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0058)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0056)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy067) from (by
          unfold
            nb074AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0062)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy068 x) from (by
          unfold
            nb074AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy065)
        from (by
          unfold
            nb074AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0060)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy066 x) from (by
          unfold
            nb074AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy061), (nb074AlphaDummy064 x)), ((nb074AlphaDummy060),
        (nb074AlphaDummy063 x)), ((nb074AlphaDummy059), (nb074AlphaDummy062 x)),
        ((nb074AlphaDummy057), (nb074AlphaDummy058 x)), ((nb074AlphaDummy053),
        (nb074AlphaDummy055 x)), ((nb074AlphaDummy054), (nb074AlphaDummy056 x)),
        ((nb074AlphaDummy046), (nb074AlphaDummy048 x)), ((nb074AlphaDummy045),
        (nb074AlphaDummy047 x)), ((nb074AlphaDummy051), (nb074AlphaDummy052 x)),
        ((nb074AlphaDummy049), (nb074AlphaDummy050 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy055 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy060) ≠
        (nb074AlphaDummy071) from (by
          unfold
            nb074AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy072 x) from (by
          unfold
            nb074AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy060) ≠
        (nb074AlphaDummy071) from (by
          unfold
            nb074AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0066)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy072 x) from (by
          unfold
            nb074AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy060) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0064)
                  0)))) (show (nb074AlphaDummy063 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy055 x))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy073) from (by
          unfold
            nb074AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy074 x) from (by
          unfold
            nb074AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy061) ≠
        (nb074AlphaDummy073) from (by
          unfold
            nb074AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0070)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy074 x) from (by
          unfold
            nb074AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy061) ≠ (nb074AlphaDummy069)
        from (by
          unfold
            nb074AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0068)
                  0)))) (show (nb074AlphaDummy064 x) ≠ (nb074AlphaDummy070 x) from (by
          unfold
            nb074AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb074AlphaDummy057),
        (nb074AlphaDummy058 x)), ((nb074AlphaDummy053), (nb074AlphaDummy055 x)),
        ((nb074AlphaDummy054), (nb074AlphaDummy056 x)), ((nb074AlphaDummy046),
        (nb074AlphaDummy048 x)), ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
        ((nb074AlphaDummy051), (nb074AlphaDummy052 x)), ((nb074AlphaDummy049),
        (nb074AlphaDummy050 x)), ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy053) ≠ (nb074AlphaDummy057) from (by
          unfold nb074AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0052) 0)))) (show (nb074AlphaDummy055 x) ≠
        (nb074AlphaDummy058 x) from (by
          unfold nb074AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb074AlphaDummy057),
        (nb074AlphaDummy058 x)), ((nb074AlphaDummy053), (nb074AlphaDummy055 x)),
        ((nb074AlphaDummy054), (nb074AlphaDummy056 x)), ((nb074AlphaDummy046),
        (nb074AlphaDummy048 x)), ((nb074AlphaDummy045), (nb074AlphaDummy047 x)),
        ((nb074AlphaDummy051), (nb074AlphaDummy052 x)), ((nb074AlphaDummy049),
        (nb074AlphaDummy050 x)), ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)), ((nb074AlphaDummy001),
        (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
        (nb074AlphaDummy004 x))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb074SplitAlpha0003 x)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb074SplitAlpha0003 x)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part009`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb074_split_alpha_0005`. -/
@[expose]
noncomputable def nb074SplitAlpha0005 (x : Var) :
    TAlphaWff
      [((nb074AlphaDummy093), (nb074AlphaDummy094 x)),
        ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
        ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy093))
          (Class.cab (nb074AlphaDummy087)
            (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
              (Wff.classEq (Class.cv (nb074AlphaDummy087))
                (synCphi (Class.cv (nb074AlphaDummy088))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy093)) (Class.cab (nb074AlphaDummy087)
              (synWrex (nb074AlphaDummy088) (Class.cv (nb074AlphaDummy081))
                (Wff.classEq (Class.cv (nb074AlphaDummy087))
                  (synCphi (Class.cv (nb074AlphaDummy088)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy094 x))
          (Class.cab (nb074AlphaDummy089 x)
            (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                (synCphi (Class.cv (nb074AlphaDummy090 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy094 x))
            (Class.cab (nb074AlphaDummy089 x)
              (synWrex (nb074AlphaDummy090 x) (Class.cv (nb074AlphaDummy083 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy089 x))
                  (synCphi (Class.cv (nb074AlphaDummy090 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy088) from
                    (by
                      unfold nb074AlphaDummy088;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))))
                  (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy090 x) from (by
                      unfold nb074AlphaDummy090;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 1))))
                  (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy087) from
                      (by
                        unfold nb074AlphaDummy087;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 0))))
                    (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy089 x) from (by
                        unfold nb074AlphaDummy089;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0088 x) 0)))) (TAlphaVar.there
                      (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy093) from (by
                          unfold nb074AlphaDummy093;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0090) 0))))
                      (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy094 x) from (by
                          unfold nb074AlphaDummy094;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0091 x) 0))))
                      (TAlphaVar.there
                        (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy091) from (by
                            unfold nb074AlphaDummy091;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0087) 0))))
                        (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy092 x) from (by
                            unfold nb074AlphaDummy092;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0089 x) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074AlphaDummy000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv x)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy081))).fv ∪
                      ((Class.cv (nb074AlphaDummy082))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb074AlphaDummy083 x))).fv ∪
                      ((Class.cv (nb074AlphaDummy084 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy095) from (by
                              unfold nb074AlphaDummy095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0092) 0))))
                          (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy097 x) from (by
                              unfold nb074AlphaDummy097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0093 x) 0))))
                          (TAlphaVar.there
                            (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy096) from (by
                                unfold nb074AlphaDummy096;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0092) 1))))
                            (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy098 x) from (by
                                unfold nb074AlphaDummy098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0093 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074AlphaDummy088))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074AlphaDummy090 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy095) ≠ (nb074AlphaDummy102) from (by
          unfold nb074AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 1)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy105 x) from (by
          unfold nb074AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy095) ≠ (nb074AlphaDummy101) from (by
          unfold nb074AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 0)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy104 x) from (by
          unfold nb074AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
          unfold nb074AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0094) 0)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy100 x) from (by
          unfold nb074AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0095 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy103), (nb074AlphaDummy106 x)), ((nb074AlphaDummy102),
        (nb074AlphaDummy105 x)), ((nb074AlphaDummy101), (nb074AlphaDummy104 x)),
        ((nb074AlphaDummy099), (nb074AlphaDummy100 x)), ((nb074AlphaDummy095),
        (nb074AlphaDummy097 x)), ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
        ((nb074AlphaDummy088), (nb074AlphaDummy090 x)), ((nb074AlphaDummy087),
        (nb074AlphaDummy089 x)), ((nb074AlphaDummy093), (nb074AlphaDummy094 x)),
        ((nb074AlphaDummy091), (nb074AlphaDummy092 x)), ((nb074AlphaDummy082),
        (nb074AlphaDummy084 x)), ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy109) from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy109)
        from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy109) from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy109)
        from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy103), (nb074AlphaDummy106 x)), ((nb074AlphaDummy102),
        (nb074AlphaDummy105 x)), ((nb074AlphaDummy101), (nb074AlphaDummy104 x)),
        ((nb074AlphaDummy099), (nb074AlphaDummy100 x)), ((nb074AlphaDummy095),
        (nb074AlphaDummy097 x)), ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
        ((nb074AlphaDummy088), (nb074AlphaDummy090 x)), ((nb074AlphaDummy087),
        (nb074AlphaDummy089 x)), ((nb074AlphaDummy093), (nb074AlphaDummy094 x)),
        ((nb074AlphaDummy091), (nb074AlphaDummy092 x)), ((nb074AlphaDummy082),
        (nb074AlphaDummy084 x)), ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy097 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy102) ≠
        (nb074AlphaDummy113) from (by
          unfold
            nb074AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy114 x) from (by
          unfold
            nb074AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy113)
        from (by
          unfold
            nb074AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy114 x) from (by
          unfold
            nb074AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy115) from (by
          unfold
            nb074AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy116 x) from (by
          unfold
            nb074AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠
        (nb074AlphaDummy115) from (by
          unfold
            nb074AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy116 x) from (by
          unfold
            nb074AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
                                        unfold nb074AlphaDummy099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074AlphaDummy097 x) ≠
                                        (nb074AlphaDummy100 x) from (by
                                        unfold nb074AlphaDummy100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb074AlphaDummy099), (nb074AlphaDummy100 x)),
                                    ((nb074AlphaDummy095), (nb074AlphaDummy097 x)),
                                    ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
                                    ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
                                    ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
                                    ((nb074AlphaDummy093), (nb074AlphaDummy094 x)),
                                    ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
                                    ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                    ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                    ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                    ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                    ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                    ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                    ((nb074AlphaDummy000), x),
                                    ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from
                                    (by
                                      unfold nb074AlphaDummy099;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0094)
                                              0)))) (show
                                    (nb074AlphaDummy097 x) ≠ (nb074AlphaDummy100 x) from
                                    (by
                                      unfold nb074AlphaDummy100;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0095 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
                                        unfold nb074AlphaDummy099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074AlphaDummy097 x) ≠
                                        (nb074AlphaDummy100 x) from (by
                                        unfold nb074AlphaDummy100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb074AlphaDummy099), (nb074AlphaDummy100 x)),
                                    ((nb074AlphaDummy095), (nb074AlphaDummy097 x)),
                                    ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
                                    ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
                                    ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
                                    ((nb074AlphaDummy093), (nb074AlphaDummy094 x)),
                                    ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
                                    ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                    ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                    ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                    ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                    ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                    ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                    ((nb074AlphaDummy000), x),
                                    ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy088) from
                      (by
                        unfold nb074AlphaDummy088;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))))
                    (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy090 x) from (by
                        unfold nb074AlphaDummy090;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0088 x) 1)))) (TAlphaVar.there
                      (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy087) from (by
                          unfold nb074AlphaDummy087;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0086) 0))))
                      (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy089 x) from (by
                          unfold nb074AlphaDummy089;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0088 x) 0))))
                      (TAlphaVar.there
                        (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy093) from (by
                            unfold nb074AlphaDummy093;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0090) 0))))
                        (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy094 x) from (by
                            unfold nb074AlphaDummy094;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0091 x) 0))))
                        (TAlphaVar.there
                          (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy091) from (by
                              unfold nb074AlphaDummy091;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0087) 0))))
                          (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy092 x) from (by
                              unfold nb074AlphaDummy092;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb074AlphaDummy000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv x)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb074AlphaDummy081))).fv ∪
                        ((Class.cv (nb074AlphaDummy082))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb074AlphaDummy083 x))).fv ∪
                        ((Class.cv (nb074AlphaDummy084 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy095) from (by
                                unfold nb074AlphaDummy095;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0092) 0))))
                            (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy097 x) from (by
                                unfold nb074AlphaDummy097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy096) from (by
                                  unfold nb074AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0092) 1))))
                              (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy098 x) from
                                (by
                                  unfold nb074AlphaDummy098;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0093 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb074AlphaDummy088))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb074AlphaDummy090 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy095) ≠ (nb074AlphaDummy102) from (by
          unfold nb074AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 1)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy105 x) from (by
          unfold nb074AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy095) ≠ (nb074AlphaDummy101) from (by
          unfold nb074AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 0)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy104 x) from (by
          unfold nb074AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy095) ≠ (nb074AlphaDummy099)
        from (by
          unfold nb074AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0094)
                  0)))) (show (nb074AlphaDummy097 x) ≠ (nb074AlphaDummy100 x) from (by
          unfold nb074AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0095 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy103), (nb074AlphaDummy106 x)), ((nb074AlphaDummy102),
        (nb074AlphaDummy105 x)), ((nb074AlphaDummy101), (nb074AlphaDummy104 x)),
        ((nb074AlphaDummy099), (nb074AlphaDummy100 x)), ((nb074AlphaDummy095),
        (nb074AlphaDummy097 x)), ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
        ((nb074AlphaDummy088), (nb074AlphaDummy090 x)), ((nb074AlphaDummy087),
        (nb074AlphaDummy089 x)), ((nb074AlphaDummy093), (nb074AlphaDummy094 x)),
        ((nb074AlphaDummy091), (nb074AlphaDummy092 x)), ((nb074AlphaDummy082),
        (nb074AlphaDummy084 x)), ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy109) from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy109)
        from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy109) from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy109)
        from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy103), (nb074AlphaDummy106 x)), ((nb074AlphaDummy102),
        (nb074AlphaDummy105 x)), ((nb074AlphaDummy101), (nb074AlphaDummy104 x)),
        ((nb074AlphaDummy099), (nb074AlphaDummy100 x)), ((nb074AlphaDummy095),
        (nb074AlphaDummy097 x)), ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
        ((nb074AlphaDummy088), (nb074AlphaDummy090 x)), ((nb074AlphaDummy087),
        (nb074AlphaDummy089 x)), ((nb074AlphaDummy093), (nb074AlphaDummy094 x)),
        ((nb074AlphaDummy091), (nb074AlphaDummy092 x)), ((nb074AlphaDummy082),
        (nb074AlphaDummy084 x)), ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy097
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy102) ≠
        (nb074AlphaDummy113) from (by
          unfold
            nb074AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy114 x) from (by
          unfold
            nb074AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy113)
        from (by
          unfold
            nb074AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy114 x) from (by
          unfold
            nb074AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy115) from (by
          unfold
            nb074AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy116 x) from (by
          unfold
            nb074AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠
        (nb074AlphaDummy115) from (by
          unfold
            nb074AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy116 x) from (by
          unfold
            nb074AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from
                                        (by
                                          unfold nb074AlphaDummy099;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0094)
                                                  0)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy100 x) from (by
                                          unfold nb074AlphaDummy100;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0095 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb074AlphaDummy099), (nb074AlphaDummy100 x)),
                                      ((nb074AlphaDummy095), (nb074AlphaDummy097 x)),
                                      ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
                                      ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
                                      ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
                                      ((nb074AlphaDummy093), (nb074AlphaDummy094 x)),
                                      ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
                                      ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                      ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                      ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                      ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                      ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                      ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                      ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
                                        (nb074AlphaDummy004 x))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
                                        unfold nb074AlphaDummy099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074AlphaDummy097 x) ≠
                                        (nb074AlphaDummy100 x) from (by
                                        unfold nb074AlphaDummy100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from
                                        (by
                                          unfold nb074AlphaDummy099;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0094)
                                                  0)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy100 x) from (by
                                          unfold nb074AlphaDummy100;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0095 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb074AlphaDummy099), (nb074AlphaDummy100 x)),
                                      ((nb074AlphaDummy095), (nb074AlphaDummy097 x)),
                                      ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
                                      ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
                                      ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
                                      ((nb074AlphaDummy093), (nb074AlphaDummy094 x)),
                                      ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
                                      ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                      ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                      ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                      ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                      ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                      ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                      ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
                                        (nb074AlphaDummy004 x))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
