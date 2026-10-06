/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C093M3Part002

/-! NF weak partition development: NAR4H5C093M3Part003. -/


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

/-- Checked nominal proof certificate identified upstream as `nb093_split_alpha_0002`. -/
@[expose]
noncomputable def nb093SplitAlpha0002 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093AlphaDummy070 A), (nb093AlphaDummy071 r)),
        ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
        ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
        ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy070 A))
          (Class.cab (nb093AlphaDummy064 A)
            (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                (synCphi (Class.cv (nb093AlphaDummy065 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy070 A))
            (Class.cab (nb093AlphaDummy064 A)
              (synWrex (nb093AlphaDummy065 A) (Class.cv (nb093AlphaDummy058 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy064 A))
                  (synCphi (Class.cv (nb093AlphaDummy065 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy071 r))
          (Class.cab (nb093AlphaDummy066 r)
            (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                (synCphi (Class.cv (nb093AlphaDummy067 r))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy071 r))
            (Class.cab (nb093AlphaDummy066 r)
              (synWrex (nb093AlphaDummy067 r) (Class.cv (nb093AlphaDummy060 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy066 r))
                  (synCphi (Class.cv (nb093AlphaDummy067 r))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy065 A) from (by
                      unfold nb093AlphaDummy065;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1))))
                  (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy067 r) from (by
                      unfold nb093AlphaDummy067;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1))))
                  (TAlphaVar.there
                    (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy064 A) from (by
                        unfold nb093AlphaDummy064;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0056 A) 0))))
                    (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy066 r) from (by
                        unfold nb093AlphaDummy066;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0058 r) 0)))) (TAlphaVar.there
                      (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy070 A) from (by
                          unfold nb093AlphaDummy070;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0060 A) 0))))
                      (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy071 r) from (by
                          unfold nb093AlphaDummy071;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0061 r) 0))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy068 A) from (by
                            unfold nb093AlphaDummy068;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0057 A) 0))))
                        (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy069 r) from (by
                            unfold nb093AlphaDummy069;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0059 r) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb093AlphaDummy001 A))).fv)
                            (by decide)) (freshVar_injective (((Class.cv r)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb093AlphaDummy058 A))).fv ∪
                      ((Class.cv (nb093AlphaDummy059 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb093AlphaDummy060 r))).fv ∪
                      ((Class.cv (nb093AlphaDummy061 r))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy072 A) from (by
                              unfold nb093AlphaDummy072;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0062 A) 0))))
                          (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy074 r) from (by
                              unfold nb093AlphaDummy074;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0063 r) 0))))
                          (TAlphaVar.there
                            (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy073 A) from (by
                                unfold nb093AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0062 A) 1))))
                            (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy075 r) from (by
                                unfold nb093AlphaDummy075;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0063 r) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb093AlphaDummy065 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb093AlphaDummy067 r))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy079 A) from (by
          unfold nb093AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A) 1)))) (show (nb093AlphaDummy074 r) ≠
        (nb093AlphaDummy082 r) from (by
          unfold nb093AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy078 A) from (by
          unfold nb093AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A) 0)))) (show (nb093AlphaDummy074 r) ≠
        (nb093AlphaDummy081 r) from (by
          unfold nb093AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from (by
          unfold nb093AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0064 A)
                  0)))) (show (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r) from (by
          unfold nb093AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0065 r)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy080 A), (nb093AlphaDummy083 r)), ((nb093AlphaDummy079 A),
        (nb093AlphaDummy082 r)), ((nb093AlphaDummy078 A), (nb093AlphaDummy081 r)),
        ((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)), ((nb093AlphaDummy072 A),
        (nb093AlphaDummy074 r)), ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
        ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A),
        (nb093AlphaDummy066 r)), ((nb093AlphaDummy070 A), (nb093AlphaDummy071 r)),
        ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy080 A), (nb093AlphaDummy083 r)), ((nb093AlphaDummy079 A),
        (nb093AlphaDummy082 r)), ((nb093AlphaDummy078 A), (nb093AlphaDummy081 r)),
        ((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)), ((nb093AlphaDummy072 A),
        (nb093AlphaDummy074 r)), ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
        ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A),
        (nb093AlphaDummy066 r)), ((nb093AlphaDummy070 A), (nb093AlphaDummy071 r)),
        ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy074
        r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy090 A) from (by
          unfold
            nb093AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy091 r) from (by
          unfold
            nb093AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy090 A) from (by
          unfold
            nb093AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy091 r) from (by
          unfold
            nb093AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy080
        A) ≠ (nb093AlphaDummy092 A) from (by
          unfold
            nb093AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy093 r) from (by
          unfold
            nb093AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy080
        A) ≠ (nb093AlphaDummy092 A) from (by
          unfold
            nb093AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy093 r) from (by
          unfold
            nb093AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from
                                      (by
                                        unfold nb093AlphaDummy076;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0064 A)
                                                0)))) (show (nb093AlphaDummy074 r) ≠
                                        (nb093AlphaDummy077 r) from (by
                                        unfold nb093AlphaDummy077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0065 r)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
                                    ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
                                    ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
                                    ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
                                    ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
                                    ((nb093AlphaDummy070 A), (nb093AlphaDummy071 r)),
                                    ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
                                    ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                    ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                    ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                    ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                    ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                    ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                    ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                                    ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                    ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                                    ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                    ((nb093AlphaDummy000 A), d),
                                    ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
                                      (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
                                      (nb093AlphaDummy005 A r d)),
                                    ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from
                                    (by
                                      unfold nb093AlphaDummy076;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0064 A)
                                              0)))) (show
                                    (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r) from
                                    (by
                                      unfold nb093AlphaDummy077;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0065 r)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from
                                      (by
                                        unfold nb093AlphaDummy076;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0064 A)
                                                0)))) (show (nb093AlphaDummy074 r) ≠
                                        (nb093AlphaDummy077 r) from (by
                                        unfold nb093AlphaDummy077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0065 r)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
                                    ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
                                    ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
                                    ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
                                    ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
                                    ((nb093AlphaDummy070 A), (nb093AlphaDummy071 r)),
                                    ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
                                    ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                    ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                    ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                    ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                    ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                    ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                    ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                                    ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                    ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                                    ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                    ((nb093AlphaDummy000 A), d),
                                    ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
                                      (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
                                      (nb093AlphaDummy005 A r d)),
                                    ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy065 A) from (by
                        unfold nb093AlphaDummy065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0056 A) 1))))
                    (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy067 r) from (by
                        unfold nb093AlphaDummy067;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0058 r) 1)))) (TAlphaVar.there
                      (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy064 A) from (by
                          unfold nb093AlphaDummy064;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0056 A) 0))))
                      (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy066 r) from (by
                          unfold nb093AlphaDummy066;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0058 r) 0))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy070 A) from (by
                            unfold nb093AlphaDummy070;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0060 A) 0))))
                        (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy071 r) from (by
                            unfold nb093AlphaDummy071;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0061 r) 0))))
                        (TAlphaVar.there
                          (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy068 A) from (by
                              unfold nb093AlphaDummy068;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0057 A) 0))))
                          (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy069 r) from (by
                              unfold nb093AlphaDummy069;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0059 r) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb093AlphaDummy001 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv r)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb093AlphaDummy058 A))).fv ∪
                        ((Class.cv (nb093AlphaDummy059 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb093AlphaDummy060 r))).fv ∪
                        ((Class.cv (nb093AlphaDummy061 r))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy072 A) from (by
                                unfold nb093AlphaDummy072;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0062 A) 0))))
                            (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy074 r) from (by
                                unfold nb093AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0063 r) 0))))
                            (TAlphaVar.there
                              (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy073 A) from
                                (by
                                  unfold nb093AlphaDummy073;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0062 A) 1))))
                              (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy075 r) from
                                (by
                                  unfold nb093AlphaDummy075;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0063 r) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb093AlphaDummy065 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb093AlphaDummy067 r))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy079 A) from (by
          unfold nb093AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A) 1)))) (show (nb093AlphaDummy074 r) ≠
        (nb093AlphaDummy082 r) from (by
          unfold nb093AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy078 A) from (by
          unfold nb093AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A)
                  0)))) (show (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy081 r) from (by
          unfold nb093AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy072 A) ≠
        (nb093AlphaDummy076 A) from (by
          unfold nb093AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0064 A)
                  0)))) (show (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r) from (by
          unfold nb093AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0065 r)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy080 A), (nb093AlphaDummy083 r)), ((nb093AlphaDummy079 A),
        (nb093AlphaDummy082 r)), ((nb093AlphaDummy078 A), (nb093AlphaDummy081 r)),
        ((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)), ((nb093AlphaDummy072 A),
        (nb093AlphaDummy074 r)), ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
        ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A),
        (nb093AlphaDummy066 r)), ((nb093AlphaDummy070 A), (nb093AlphaDummy071 r)),
        ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy080 A), (nb093AlphaDummy083 r)), ((nb093AlphaDummy079 A),
        (nb093AlphaDummy082 r)), ((nb093AlphaDummy078 A), (nb093AlphaDummy081 r)),
        ((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)), ((nb093AlphaDummy072 A),
        (nb093AlphaDummy074 r)), ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
        ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A),
        (nb093AlphaDummy066 r)), ((nb093AlphaDummy070 A), (nb093AlphaDummy071 r)),
        ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy074 r))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy079
        A) ≠ (nb093AlphaDummy090 A) from (by
          unfold
            nb093AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy091 r) from (by
          unfold
            nb093AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy090 A) from (by
          unfold
            nb093AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy091 r) from (by
          unfold
            nb093AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy080
        A) ≠ (nb093AlphaDummy092 A) from (by
          unfold
            nb093AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy093 r) from (by
          unfold
            nb093AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy080
        A) ≠ (nb093AlphaDummy092 A) from (by
          unfold
            nb093AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy093 r) from (by
          unfold
            nb093AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A)
                                        from (by
                                          unfold nb093AlphaDummy076;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0064 A) 0)))) (show
                                        (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r)
                                        from (by
                                          unfold nb093AlphaDummy077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0065 r) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
                                      ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
                                      ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
                                      ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
                                      ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
                                      ((nb093AlphaDummy070 A), (nb093AlphaDummy071 r)),
                                      ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
                                      ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                      ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                      ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                      ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                      ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                      ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                      ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                                      ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                      ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                                      ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                      ((nb093AlphaDummy000 A), d),
                                      ((nb093AlphaDummy001 A), r),
                                      ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                                      ((nb093AlphaDummy004 A),
                                        (nb093AlphaDummy005 A r d)),
                                      ((nb093AlphaDummy002 A),
                                        (nb093AlphaDummy003 A r d))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from
                                      (by
                                        unfold nb093AlphaDummy076;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0064 A)
                                                0)))) (show (nb093AlphaDummy074 r) ≠
                                        (nb093AlphaDummy077 r) from (by
                                        unfold nb093AlphaDummy077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0065 r)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A)
                                        from (by
                                          unfold nb093AlphaDummy076;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0064 A) 0)))) (show
                                        (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r)
                                        from (by
                                          unfold nb093AlphaDummy077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0065 r) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
                                      ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
                                      ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
                                      ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
                                      ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
                                      ((nb093AlphaDummy070 A), (nb093AlphaDummy071 r)),
                                      ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
                                      ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                      ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                      ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                      ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                      ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                      ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                      ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                                      ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                      ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                                      ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                      ((nb093AlphaDummy000 A), d),
                                      ((nb093AlphaDummy001 A), r),
                                      ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                                      ((nb093AlphaDummy004 A),
                                        (nb093AlphaDummy005 A r d)),
                                      ((nb093AlphaDummy002 A),
                                        (nb093AlphaDummy003 A r d))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb093_split_alpha_0003`. -/
@[expose]
noncomputable def nb093SplitAlpha0003 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093AlphaDummy098 A), (nb093AlphaDummy099 r)),
        ((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)),
        ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
        ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
        ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)),
        ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
        ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
        ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy098 A))
          (synCphi (Class.cv (nb093AlphaDummy065 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy098 A))
            (synCphi (Class.cv (nb093AlphaDummy065 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy099 r))
          (synCphi (Class.cv (nb093AlphaDummy067 r)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy099 r))
            (synCphi (Class.cv (nb093AlphaDummy067 r)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy072 A) from (by
                      unfold nb093AlphaDummy072;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0062 A) 0))))
                  (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy074 r) from (by
                      unfold nb093AlphaDummy074;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0063 r) 0))))
                  (TAlphaVar.there
                    (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy073 A) from (by
                        unfold nb093AlphaDummy073;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0062 A) 1))))
                    (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy075 r) from (by
                        unfold nb093AlphaDummy075;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0063 r) 1)))) (TAlphaVar.there
                      (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy098 A) from (by
                          unfold nb093AlphaDummy098;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0092 A) 0))))
                      (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy099 r) from (by
                          unfold nb093AlphaDummy099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0093 r) 0))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy096 A) from (by
                            unfold nb093AlphaDummy096;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0090 A) 0))))
                        (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy097 r) from (by
                            unfold nb093AlphaDummy097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0091 r) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy065 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy067 r))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy079 A) from
                                      (by
                                        unfold nb093AlphaDummy079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0066 A)
                                                1)))) (show (nb093AlphaDummy074 r) ≠
                                        (nb093AlphaDummy082 r) from (by
                                        unfold nb093AlphaDummy082;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0067 r)
                                                1)))) (TAlphaVar.there (show
                                        (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy078 A)
                                        from (by
                                          unfold nb093AlphaDummy078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0066 A) 0)))) (show
                                        (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy081 r)
                                        from (by
                                          unfold nb093AlphaDummy081;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0067 r) 0))))
                                      (TAlphaVar.there (show (nb093AlphaDummy072 A) ≠
        (nb093AlphaDummy076 A) from (by
          unfold nb093AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0064 A) 0)))) (show (nb093AlphaDummy074 r) ≠
        (nb093AlphaDummy077 r) from (by
          unfold nb093AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0065 r) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb093AlphaDummy080 A),
        (nb093AlphaDummy083 r)), ((nb093AlphaDummy079 A), (nb093AlphaDummy082 r)),
                                        ((nb093AlphaDummy078 A), (nb093AlphaDummy081 r)),
                                        ((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
                                        ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
                                        ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
                                        ((nb093AlphaDummy098 A), (nb093AlphaDummy099 r)),
                                        ((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)),
                                        ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
                                        ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
                                        ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)),
                                        ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
                                        ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                        ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                        ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                        ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                        ((nb093AlphaDummy000 A), d),
                                        ((nb093AlphaDummy001 A), r),
                                        ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb093AlphaDummy080 A), (nb093AlphaDummy083 r)),
        ((nb093AlphaDummy079 A), (nb093AlphaDummy082 r)), ((nb093AlphaDummy078 A),
        (nb093AlphaDummy081 r)), ((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
        ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)), ((nb093AlphaDummy073 A),
        (nb093AlphaDummy075 r)), ((nb093AlphaDummy098 A), (nb093AlphaDummy099 r)),
        ((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)), ((nb093AlphaDummy065 A),
        (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
        ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)), ((nb093AlphaDummy068 A),
        (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy090 A) from (by
          unfold
            nb093AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy091 r) from (by
          unfold
            nb093AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy090 A) from (by
          unfold
            nb093AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy091 r) from (by
          unfold
            nb093AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy092 A) from (by
          unfold
            nb093AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy093 r) from (by
          unfold
            nb093AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy092 A) from (by
          unfold
            nb093AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy093 r) from (by
          unfold
            nb093AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from (by
                                unfold nb093AlphaDummy076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                            (show (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r) from (by
                                unfold nb093AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
                            ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
                            ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
                            ((nb093AlphaDummy098 A), (nb093AlphaDummy099 r)),
                            ((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)),
                            ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
                            ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
                            ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)),
                            ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
                            ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                            ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                            ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                            ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                            ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                            ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                            ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                            ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                            ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                            ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                            ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                            ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                            ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                            ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from (by
                              unfold nb093AlphaDummy076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                          (show (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r) from (by
                              unfold nb093AlphaDummy077;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from (by
                                unfold nb093AlphaDummy076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                            (show (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r) from (by
                                unfold nb093AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
                            ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
                            ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
                            ((nb093AlphaDummy098 A), (nb093AlphaDummy099 r)),
                            ((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)),
                            ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
                            ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
                            ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)),
                            ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
                            ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                            ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                            ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                            ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                            ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                            ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                            ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                            ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                            ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                            ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                            ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                            ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                            ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                            ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy072 A) from (by
                        unfold nb093AlphaDummy072;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0062 A) 0))))
                    (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy074 r) from (by
                        unfold nb093AlphaDummy074;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0063 r) 0)))) (TAlphaVar.there
                      (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy073 A) from (by
                          unfold nb093AlphaDummy073;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0062 A) 1))))
                      (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy075 r) from (by
                          unfold nb093AlphaDummy075;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0063 r) 1))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy098 A) from (by
                            unfold nb093AlphaDummy098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0092 A) 0))))
                        (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy099 r) from (by
                            unfold nb093AlphaDummy099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0093 r) 0))))
                        (TAlphaVar.there
                          (show (nb093AlphaDummy065 A) ≠ (nb093AlphaDummy096 A) from (by
                              unfold nb093AlphaDummy096;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0090 A) 0))))
                          (show (nb093AlphaDummy067 r) ≠ (nb093AlphaDummy097 r) from (by
                              unfold nb093AlphaDummy097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0091 r) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb093AlphaDummy065 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb093AlphaDummy067 r))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb093AlphaDummy072 A) ≠
        (nb093AlphaDummy079 A) from (by
                                          unfold nb093AlphaDummy079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0066 A) 1)))) (show
                                        (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy082 r)
                                        from (by
                                          unfold nb093AlphaDummy082;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0067 r) 1))))
                                      (TAlphaVar.there (show (nb093AlphaDummy072 A) ≠
        (nb093AlphaDummy078 A) from (by
          unfold nb093AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0066 A) 0)))) (show (nb093AlphaDummy074 r) ≠
        (nb093AlphaDummy081 r) from (by
          unfold nb093AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0067 r) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from (by
          unfold nb093AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0064 A) 0)))) (show (nb093AlphaDummy074 r) ≠
        (nb093AlphaDummy077 r) from (by
          unfold nb093AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0065 r) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb093AlphaDummy080 A),
        (nb093AlphaDummy083 r)), ((nb093AlphaDummy079 A), (nb093AlphaDummy082 r)),
        ((nb093AlphaDummy078 A), (nb093AlphaDummy081 r)), ((nb093AlphaDummy076 A),
        (nb093AlphaDummy077 r)), ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
        ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)), ((nb093AlphaDummy098 A),
        (nb093AlphaDummy099 r)), ((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)),
        ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A),
        (nb093AlphaDummy066 r)), ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)),
        ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0070
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0071
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0068
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0069
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy086 A) from (by
          unfold
            nb093AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0074
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy087 r) from (by
          unfold
            nb093AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0075
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy084 A) from (by
          unfold
            nb093AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0072
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy085 r) from (by
          unfold
            nb093AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0073
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy080 A), (nb093AlphaDummy083 r)), ((nb093AlphaDummy079 A),
        (nb093AlphaDummy082 r)), ((nb093AlphaDummy078 A), (nb093AlphaDummy081 r)),
        ((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)), ((nb093AlphaDummy072 A),
        (nb093AlphaDummy074 r)), ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
        ((nb093AlphaDummy098 A), (nb093AlphaDummy099 r)), ((nb093AlphaDummy096 A),
        (nb093AlphaDummy097 r)), ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
        ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)), ((nb093AlphaDummy094 A),
        (nb093AlphaDummy095 r)), ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
        ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A),
        (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
        ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A),
        (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A),
        (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093AlphaDummy072 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy090 A) from (by
          unfold
            nb093AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy091 r) from (by
          unfold
            nb093AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠ (nb093AlphaDummy090 A) from (by
          unfold
            nb093AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0078
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy091 r) from (by
          unfold
            nb093AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0079
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy079 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0076
                    A)
                  0)))) (show (nb093AlphaDummy082 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0077
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy072
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy074 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy092 A) from (by
          unfold
            nb093AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy093 r) from (by
          unfold
            nb093AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy080 A) ≠ (nb093AlphaDummy092 A) from (by
          unfold
            nb093AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0082
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy093 r) from (by
          unfold
            nb093AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0083
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy080 A) ≠
        (nb093AlphaDummy088 A) from (by
          unfold
            nb093AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0080
                    A)
                  0)))) (show (nb093AlphaDummy083 r) ≠ (nb093AlphaDummy089 r) from (by
          unfold
            nb093AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0081
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from
                                (by
                                  unfold nb093AlphaDummy076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                              (show (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r) from
                                (by
                                  unfold nb093AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
                              ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
                              ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
                              ((nb093AlphaDummy098 A), (nb093AlphaDummy099 r)),
                              ((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)),
                              ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
                              ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
                              ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)),
                              ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
                              ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                              ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                              ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                              ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                              ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                              ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                              ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                              ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                              ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                              ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                              ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                              ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                              ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                              ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from (by
                                unfold nb093AlphaDummy076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                            (show (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r) from (by
                                unfold nb093AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb093AlphaDummy072 A) ≠ (nb093AlphaDummy076 A) from
                                (by
                                  unfold nb093AlphaDummy076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0064 A) 0))))
                              (show (nb093AlphaDummy074 r) ≠ (nb093AlphaDummy077 r) from
                                (by
                                  unfold nb093AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0065 r) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb093AlphaDummy076 A), (nb093AlphaDummy077 r)),
                              ((nb093AlphaDummy072 A), (nb093AlphaDummy074 r)),
                              ((nb093AlphaDummy073 A), (nb093AlphaDummy075 r)),
                              ((nb093AlphaDummy098 A), (nb093AlphaDummy099 r)),
                              ((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)),
                              ((nb093AlphaDummy065 A), (nb093AlphaDummy067 r)),
                              ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
                              ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)),
                              ((nb093AlphaDummy068 A), (nb093AlphaDummy069 r)),
                              ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                              ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                              ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                              ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                              ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                              ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                              ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                              ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                              ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                              ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                              ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                              ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                              ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                              ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
