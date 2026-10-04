/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C093M3Part004

/-! NF weak partition development: NAR4H5C093M3Part005. -/


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

/-- Checked nominal proof certificate identified upstream as `nb093_split_alpha_0007`. -/
@[expose]
noncomputable def nb093SplitAlpha0007 (A : Class) (r : Var) (d : Var)
    (dv_d_r : d ≠ r) :
    TAlphaWff
      [((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy050 A))
          (Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
              (synCdif (Class.cv (nb093AlphaDummy001 A))
                (synCcnv (Class.cv (nb093AlphaDummy001 A))))
              (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                (synCphi (Class.cv (nb093AlphaDummy045 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy050 A))
            (Class.cab (nb093AlphaDummy044 A) (synWrex (nb093AlphaDummy045 A)
                (synCdif (Class.cv (nb093AlphaDummy001 A))
                  (synCcnv (Class.cv (nb093AlphaDummy001 A))))
                (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
                  (synCphi (Class.cv (nb093AlphaDummy045 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy051 r d))
          (Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
              (synCdif (Class.cv r) (synCcnv (Class.cv r)))
              (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                (synCphi (Class.cv (nb093AlphaDummy047 r d))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy051 r d))
            (Class.cab (nb093AlphaDummy046 r d) (synWrex (nb093AlphaDummy047 r d)
                (synCdif (Class.cv r) (synCcnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
                  (synCphi (Class.cv (nb093AlphaDummy047 r d))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy054 A) from
                                    (by
                                      unfold nb093AlphaDummy054;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0050 A)
                                              0)))) (show r ≠ (nb093AlphaDummy055 r) from (by
                                      unfold nb093AlphaDummy055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0051 r)
                                              0)))) (TAlphaVar.there (show
                                      (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy052 A) from
                                      (by
                                        unfold nb093AlphaDummy052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0048 A)
                                                0)))) (show r ≠ (nb093AlphaDummy053 r) from
                                      (by
                                        unfold nb093AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0049 r)
                                                0)))) (TAlphaVar.there (show
                                        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy045 A)
                                        from (by
                                          unfold nb093AlphaDummy045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0042 A) 1))))
                                      (show r ≠ (nb093AlphaDummy047 r d) from (by
                                          unfold nb093AlphaDummy047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0044 r d) 1))))
                                      (TAlphaVar.there (show (nb093AlphaDummy001 A) ≠
        (nb093AlphaDummy044 A) from (by
          unfold nb093AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 0)))) (show r ≠ (nb093AlphaDummy046 r d) from
        (by
          unfold nb093AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy050 A) from (by
          unfold nb093AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0046 A) 0)))) (show r ≠ (nb093AlphaDummy051 r d) from
        (by
          unfold nb093AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0047 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy048 A) from (by
          unfold nb093AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093AlphaDummy049 r d) from
        (by
          unfold nb093AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_d_r)
        (TAlphaVar.here _ _ _))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb093SplitAlpha0006 A r d dv_d_r)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy054 A) from
                                    (by
                                      unfold nb093AlphaDummy054;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0050 A)
                                              0)))) (show r ≠ (nb093AlphaDummy055 r) from (by
                                      unfold nb093AlphaDummy055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0051 r)
                                              0)))) (TAlphaVar.there (show
                                      (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy052 A) from
                                      (by
                                        unfold nb093AlphaDummy052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0048 A)
                                                0)))) (show r ≠ (nb093AlphaDummy053 r) from
                                      (by
                                        unfold nb093AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0049 r)
                                                0)))) (TAlphaVar.there (show
                                        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy045 A)
                                        from (by
                                          unfold nb093AlphaDummy045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0042 A) 1))))
                                      (show r ≠ (nb093AlphaDummy047 r d) from (by
                                          unfold nb093AlphaDummy047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0044 r d) 1))))
                                      (TAlphaVar.there (show (nb093AlphaDummy001 A) ≠
        (nb093AlphaDummy044 A) from (by
          unfold nb093AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 0)))) (show r ≠ (nb093AlphaDummy046 r d) from
        (by
          unfold nb093AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy050 A) from (by
          unfold nb093AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0046 A) 0)))) (show r ≠ (nb093AlphaDummy051 r d) from
        (by
          unfold nb093AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0047 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy048 A) from (by
          unfold nb093AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093AlphaDummy049 r d) from
        (by
          unfold nb093AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_d_r)
        (TAlphaVar.here _ _ _))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb093SplitAlpha0006 A r d dv_d_r)))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((synCdif (Class.cv (nb093AlphaDummy001 A))
                          (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
                      ((Class.cv (nb093AlphaDummy000 A))).fv) (by decide))
                  (freshVar_injective (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪
                      ((Class.cv d)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093AlphaDummy045 A) ≠ (nb093AlphaDummy136 A) from (by
                              unfold nb093AlphaDummy136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0138 A) 0))))
                          (show (nb093AlphaDummy047 r d) ≠ (nb093AlphaDummy138 r d) from
                            (by
                              unfold nb093AlphaDummy138;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0139 r d) 0))))
                          (TAlphaVar.there
                            (show (nb093AlphaDummy045 A) ≠ (nb093AlphaDummy137 A) from (by
                                unfold nb093AlphaDummy137;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0138 A) 1)))) (show
                              (nb093AlphaDummy047 r d) ≠ (nb093AlphaDummy139 r d) from (by
                                unfold nb093AlphaDummy139;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0139 r d) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb093AlphaDummy045 A))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb093AlphaDummy047 r d))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy143 A) from (by
          unfold nb093AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142 A) 1)))) (show (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy146 r d) from (by
          unfold nb093AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143 r d) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy142 A) from (by
          unfold nb093AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142 A) 0)))) (show (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy145 r d) from (by
          unfold nb093AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143 r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠
        (nb093AlphaDummy140 A) from (by
          unfold nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A)
                  0)))) (show (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy141 r d) from (by
          unfold nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy144 A), (nb093AlphaDummy147 r d)), ((nb093AlphaDummy143 A),
        (nb093AlphaDummy146 r d)), ((nb093AlphaDummy142 A), (nb093AlphaDummy145 r d)),
        ((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A),
        (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy144 A), (nb093AlphaDummy147 r d)), ((nb093AlphaDummy143 A),
        (nb093AlphaDummy146 r d)), ((nb093AlphaDummy142 A), (nb093AlphaDummy145 r d)),
        ((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A),
        (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r
        d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy154 A) from (by
          unfold
            nb093AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy155 r d) from (by
          unfold
            nb093AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy154 A) from (by
          unfold
            nb093AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy155 r d) from (by
          unfold
            nb093AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy156 A) from (by
          unfold
            nb093AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy157 r d) from (by
          unfold
            nb093AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy156 A) from (by
          unfold
            nb093AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy157 r d) from (by
          unfold
            nb093AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A) from
                                      (by
                                        unfold nb093AlphaDummy140;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0140 A)
                                                0)))) (show (nb093AlphaDummy138 r d) ≠
                                        (nb093AlphaDummy141 r d) from (by
                                        unfold nb093AlphaDummy141;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0141 r d) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)),
                                    ((nb093AlphaDummy136 A), (nb093AlphaDummy138 r d)),
                                    ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
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
                                    (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A) from
                                    (by
                                      unfold nb093AlphaDummy140;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0140 A)
                                              0)))) (show (nb093AlphaDummy138 r d) ≠
                                      (nb093AlphaDummy141 r d) from (by
                                      unfold nb093AlphaDummy141;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0141 r d)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A) from
                                      (by
                                        unfold nb093AlphaDummy140;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0140 A)
                                                0)))) (show (nb093AlphaDummy138 r d) ≠
                                        (nb093AlphaDummy141 r d) from (by
                                        unfold nb093AlphaDummy141;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0141 r d) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)),
                                    ((nb093AlphaDummy136 A), (nb093AlphaDummy138 r d)),
                                    ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
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
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy054 A) from
                                      (by
                                        unfold nb093AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0050 A)
                                                0)))) (show r ≠ (nb093AlphaDummy055 r) from
                                      (by
                                        unfold nb093AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0051 r)
                                                0)))) (TAlphaVar.there (show
                                        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy052 A)
                                        from (by
                                          unfold nb093AlphaDummy052;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0048 A) 0))))
                                      (show r ≠ (nb093AlphaDummy053 r) from (by
                                          unfold nb093AlphaDummy053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0049 r) 0))))
                                      (TAlphaVar.there (show (nb093AlphaDummy001 A) ≠
        (nb093AlphaDummy045 A) from (by
          unfold nb093AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 1)))) (show r ≠ (nb093AlphaDummy047 r d) from
        (by
          unfold nb093AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy044 A) from (by
          unfold nb093AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 0)))) (show r ≠ (nb093AlphaDummy046 r d) from
        (by
          unfold nb093AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy050 A) from (by
          unfold nb093AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0046 A) 0)))) (show r ≠ (nb093AlphaDummy051 r d) from
        (by
          unfold nb093AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0047 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy048 A) from (by
          unfold nb093AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093AlphaDummy049 r d) from
        (by
          unfold nb093AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
        (Ne.symm dv_d_r) (TAlphaVar.here _ _ _))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                      (nb093SplitAlpha0006 A r d dv_d_r)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy054 A) from
                                      (by
                                        unfold nb093AlphaDummy054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0050 A)
                                                0)))) (show r ≠ (nb093AlphaDummy055 r) from
                                      (by
                                        unfold nb093AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0051 r)
                                                0)))) (TAlphaVar.there (show
                                        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy052 A)
                                        from (by
                                          unfold nb093AlphaDummy052;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0048 A) 0))))
                                      (show r ≠ (nb093AlphaDummy053 r) from (by
                                          unfold nb093AlphaDummy053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0049 r) 0))))
                                      (TAlphaVar.there (show (nb093AlphaDummy001 A) ≠
        (nb093AlphaDummy045 A) from (by
          unfold nb093AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 1)))) (show r ≠ (nb093AlphaDummy047 r d) from
        (by
          unfold nb093AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy044 A) from (by
          unfold nb093AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0042 A) 0)))) (show r ≠ (nb093AlphaDummy046 r d) from
        (by
          unfold nb093AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0044 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy050 A) from (by
          unfold nb093AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0046 A) 0)))) (show r ≠ (nb093AlphaDummy051 r d) from
        (by
          unfold nb093AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0047 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy048 A) from (by
          unfold nb093AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093AlphaDummy049 r d) from
        (by
          unfold nb093AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
        (Ne.symm dv_d_r) (TAlphaVar.here _ _ _))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                      (nb093SplitAlpha0006 A r d dv_d_r)))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((synCdif (Class.cv (nb093AlphaDummy001 A))
                            (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
                        ((Class.cv (nb093AlphaDummy000 A))).fv) (by decide))
                    (freshVar_injective (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪
                        ((Class.cv d)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093AlphaDummy045 A) ≠ (nb093AlphaDummy136 A) from (by
                                unfold nb093AlphaDummy136;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0138 A) 0)))) (show
                              (nb093AlphaDummy047 r d) ≠ (nb093AlphaDummy138 r d) from (by
                                unfold nb093AlphaDummy138;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0139 r d) 0))))
                            (TAlphaVar.there
                              (show (nb093AlphaDummy045 A) ≠ (nb093AlphaDummy137 A) from
                                (by
                                  unfold nb093AlphaDummy137;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0138 A) 1)))) (show
                                (nb093AlphaDummy047 r d) ≠ (nb093AlphaDummy139 r d) from
                                (by
                                  unfold nb093AlphaDummy139;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0139 r d)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb093AlphaDummy045 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb093AlphaDummy047 r d))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy143 A) from (by
          unfold nb093AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142 A) 1)))) (show (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy146 r d) from (by
          unfold nb093AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143 r d)
                  1)))) (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠
        (nb093AlphaDummy142 A) from (by
          unfold nb093AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142 A)
                  0)))) (show (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy145 r d) from (by
          unfold nb093AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143 r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠
        (nb093AlphaDummy140 A) from (by
          unfold nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A)
                  0)))) (show (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy141 r d) from (by
          unfold nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy144 A), (nb093AlphaDummy147 r d)), ((nb093AlphaDummy143 A),
        (nb093AlphaDummy146 r d)), ((nb093AlphaDummy142 A), (nb093AlphaDummy145 r d)),
        ((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A),
        (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy144 A), (nb093AlphaDummy147 r d)), ((nb093AlphaDummy143 A),
        (nb093AlphaDummy146 r d)), ((nb093AlphaDummy142 A), (nb093AlphaDummy145 r d)),
        ((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A),
        (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy143
        A) ≠ (nb093AlphaDummy154 A) from (by
          unfold
            nb093AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy155 r d) from (by
          unfold
            nb093AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy154 A) from (by
          unfold
            nb093AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy155 r d) from (by
          unfold
            nb093AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy156 A) from (by
          unfold
            nb093AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy157 r d) from (by
          unfold
            nb093AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy156 A) from (by
          unfold
            nb093AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy157 r d) from (by
          unfold
            nb093AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A)
                                        from (by
                                          unfold nb093AlphaDummy140;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0140 A) 0)))) (show
                                        (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy141 r d) from (by
                                          unfold nb093AlphaDummy141;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0141 r d) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)),
                                      ((nb093AlphaDummy136 A), (nb093AlphaDummy138 r d)),
                                      ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
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
                                      (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A) from
                                      (by
                                        unfold nb093AlphaDummy140;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0140 A)
                                                0)))) (show (nb093AlphaDummy138 r d) ≠
                                        (nb093AlphaDummy141 r d) from (by
                                        unfold nb093AlphaDummy141;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0141 r d) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A)
                                        from (by
                                          unfold nb093AlphaDummy140;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0140 A) 0)))) (show
                                        (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy141 r d) from (by
                                          unfold nb093AlphaDummy141;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0141 r d) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)),
                                      ((nb093AlphaDummy136 A), (nb093AlphaDummy138 r d)),
                                      ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
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

/-- Checked nominal proof certificate identified upstream as `nb093_split_alpha_0008`. -/
@[expose]
noncomputable def nb093SplitAlpha0008 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy158 A), (nb093AlphaDummy159 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy045 A))
          (Class.cv (nb093AlphaDummy000 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb093AlphaDummy044 A))
            (synCun (synCphi (Class.cv (nb093AlphaDummy045 A))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy047 r d)) (Class.cv d)) (Wff.neg
          (Wff.classEq (Class.cv (nb093AlphaDummy046 r d))
            (synCun (synCphi (Class.cv (nb093AlphaDummy047 r d)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy045 A) from (by
              unfold nb093AlphaDummy045;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 1))))
          (show d ≠ (nb093AlphaDummy047 r d) from (by
              unfold nb093AlphaDummy047;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 1))))
          (TAlphaVar.there (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy044 A) from (by
                unfold nb093AlphaDummy044;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 0))))
            (show d ≠ (nb093AlphaDummy046 r d) from (by
                unfold nb093AlphaDummy046;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 0))))
            (TAlphaVar.there (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy158 A) from
                (by
                  unfold nb093AlphaDummy158;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0164 A) 0))))
              (show d ≠ (nb093AlphaDummy159 r d) from (by
                  unfold nb093AlphaDummy159;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0165 r d) 0))))
              (TAlphaVar.there (show (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy048 A) from
                  (by
                    unfold nb093AlphaDummy048;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0161 A) 0))))
                (show d ≠ (nb093AlphaDummy049 r d) from (by
                    unfold nb093AlphaDummy049;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0163 r d) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((synCdif (Class.cv (nb093AlphaDummy001 A))
                    (synCcnv (Class.cv (nb093AlphaDummy001 A))))).fv ∪
                ((Class.cv (nb093AlphaDummy000 A))).fv) (by decide)) (freshVar_injective
              (((synCdif (Class.cv r) (synCcnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv)
              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy045 A) ≠ (nb093AlphaDummy136 A) from
                                      (by
                                        unfold nb093AlphaDummy136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0138 A)
                                                0)))) (show (nb093AlphaDummy047 r d) ≠
                                        (nb093AlphaDummy138 r d) from (by
                                        unfold nb093AlphaDummy138;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0139 r d) 0))))
                                    (TAlphaVar.there (show (nb093AlphaDummy045 A) ≠
        (nb093AlphaDummy137 A) from (by
                                          unfold nb093AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0138 A) 1)))) (show
                                        (nb093AlphaDummy047 r d) ≠
        (nb093AlphaDummy139 r d) from (by
                                          unfold nb093AlphaDummy139;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0139 r d) 1))))
                                      (TAlphaVar.there (show (nb093AlphaDummy045 A) ≠
        (nb093AlphaDummy162 A) from (by
          unfold nb093AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0168 A) 0)))) (show (nb093AlphaDummy047 r d) ≠
        (nb093AlphaDummy163 r d) from (by
          unfold nb093AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0169 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy045 A) ≠ (nb093AlphaDummy160 A) from (by
          unfold nb093AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0166 A) 0)))) (show (nb093AlphaDummy047 r d) ≠
        (nb093AlphaDummy161 r d) from (by
          unfold nb093AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0167 r d) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb093AlphaDummy045 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb093AlphaDummy047 r d))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy143 A) from (by
          unfold nb093AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142
                    A)
                  1)))) (show (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy146 r d) from (by
          unfold nb093AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143
                    r d)
                  1)))) (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠
        (nb093AlphaDummy142 A) from (by
          unfold nb093AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142
                    A)
                  0)))) (show (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy145 r d) from (by
          unfold nb093AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠
        (nb093AlphaDummy140 A) from (by
          unfold
            nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140
                    A)
                  0)))) (show (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy141 r d) from (by
          unfold
            nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy144 A), (nb093AlphaDummy147 r d)), ((nb093AlphaDummy143 A),
        (nb093AlphaDummy146 r d)), ((nb093AlphaDummy142 A), (nb093AlphaDummy145 r d)),
        ((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy162 A), (nb093AlphaDummy163 r d)), ((nb093AlphaDummy160 A),
        (nb093AlphaDummy161 r d)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy158 A),
        (nb093AlphaDummy159 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy144 A), (nb093AlphaDummy147 r d)), ((nb093AlphaDummy143 A),
        (nb093AlphaDummy146 r d)), ((nb093AlphaDummy142 A), (nb093AlphaDummy145 r d)),
        ((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy162 A), (nb093AlphaDummy163 r d)), ((nb093AlphaDummy160 A),
        (nb093AlphaDummy161 r d)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy158 A),
        (nb093AlphaDummy159 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138
        r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy154 A) from (by
          unfold
            nb093AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy155 r d) from (by
          unfold
            nb093AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy143
        A) ≠ (nb093AlphaDummy154 A) from (by
          unfold
            nb093AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy155 r d) from (by
          unfold
            nb093AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠ (nb093AlphaDummy156 A) from (by
          unfold
            nb093AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy157 r d) from (by
          unfold
            nb093AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy156 A) from (by
          unfold
            nb093AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy157 r d) from (by
          unfold
            nb093AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠
        (nb093AlphaDummy140 A) from (by
          unfold nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy141 r d) from (by
          unfold nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy162 A), (nb093AlphaDummy163 r d)), ((nb093AlphaDummy160 A),
        (nb093AlphaDummy161 r d)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy158 A),
        (nb093AlphaDummy159 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A) from (by
          unfold nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy141 r d) from (by
          unfold nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A) from (by
          unfold nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy141 r d) from (by
          unfold nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy162 A), (nb093AlphaDummy163 r d)), ((nb093AlphaDummy160 A),
        (nb093AlphaDummy161 r d)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy158 A),
        (nb093AlphaDummy159 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy045 A) ≠ (nb093AlphaDummy136 A) from
                                      (by
                                        unfold nb093AlphaDummy136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0138 A)
                                                0)))) (show (nb093AlphaDummy047 r d) ≠
                                        (nb093AlphaDummy138 r d) from (by
                                        unfold nb093AlphaDummy138;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0139 r d) 0))))
                                    (TAlphaVar.there (show (nb093AlphaDummy045 A) ≠
        (nb093AlphaDummy137 A) from (by
                                          unfold nb093AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0138 A) 1)))) (show
                                        (nb093AlphaDummy047 r d) ≠
        (nb093AlphaDummy139 r d) from (by
                                          unfold nb093AlphaDummy139;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0139 r d) 1))))
                                      (TAlphaVar.there (show (nb093AlphaDummy045 A) ≠
        (nb093AlphaDummy162 A) from (by
          unfold nb093AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0168 A) 0)))) (show (nb093AlphaDummy047 r d) ≠
        (nb093AlphaDummy163 r d) from (by
          unfold nb093AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0169 r d) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy045 A) ≠ (nb093AlphaDummy160 A) from (by
          unfold nb093AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0166 A) 0)))) (show (nb093AlphaDummy047 r d) ≠
        (nb093AlphaDummy161 r d) from (by
          unfold nb093AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0167 r d) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb093AlphaDummy045 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb093AlphaDummy047 r d))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy143 A) from (by
          unfold nb093AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142
                    A)
                  1)))) (show (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy146 r d) from (by
          unfold nb093AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143
                    r d)
                  1)))) (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠
        (nb093AlphaDummy142 A) from (by
          unfold nb093AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0142
                    A)
                  0)))) (show (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy145 r d) from (by
          unfold nb093AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0143
                    r d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠
        (nb093AlphaDummy140 A) from (by
          unfold
            nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140
                    A)
                  0)))) (show (nb093AlphaDummy138 r d) ≠ (nb093AlphaDummy141 r d) from (by
          unfold
            nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy144 A), (nb093AlphaDummy147 r d)), ((nb093AlphaDummy143 A),
        (nb093AlphaDummy146 r d)), ((nb093AlphaDummy142 A), (nb093AlphaDummy145 r d)),
        ((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy162 A), (nb093AlphaDummy163 r d)), ((nb093AlphaDummy160 A),
        (nb093AlphaDummy161 r d)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy158 A),
        (nb093AlphaDummy159 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0146
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0147
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0144
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0145
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy150 A) from (by
          unfold
            nb093AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0150
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy151 r d) from (by
          unfold
            nb093AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0151
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy148 A) from (by
          unfold
            nb093AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0148
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy149 r d) from (by
          unfold
            nb093AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0149
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy144 A), (nb093AlphaDummy147 r d)), ((nb093AlphaDummy143 A),
        (nb093AlphaDummy146 r d)), ((nb093AlphaDummy142 A), (nb093AlphaDummy145 r d)),
        ((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy162 A), (nb093AlphaDummy163 r d)), ((nb093AlphaDummy160 A),
        (nb093AlphaDummy161 r d)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy158 A),
        (nb093AlphaDummy159 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r
        d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138
        r d))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy136 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy154 A) from (by
          unfold
            nb093AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy155 r d) from (by
          unfold
            nb093AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy143
        A) ≠ (nb093AlphaDummy154 A) from (by
          unfold
            nb093AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0154
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy155 r d) from (by
          unfold
            nb093AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0155
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy143 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0152
                    A)
                  0)))) (show (nb093AlphaDummy146 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0153
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy136
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy138 r d))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠ (nb093AlphaDummy156 A) from (by
          unfold
            nb093AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy157 r d) from (by
          unfold
            nb093AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy144
        A) ≠ (nb093AlphaDummy156 A) from (by
          unfold
            nb093AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0158
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy157 r d) from (by
          unfold
            nb093AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0159
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy144 A) ≠
        (nb093AlphaDummy152 A) from (by
          unfold
            nb093AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0156
                    A)
                  0)))) (show (nb093AlphaDummy147 r d) ≠ (nb093AlphaDummy153 r d) from (by
          unfold
            nb093AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0157
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠
        (nb093AlphaDummy140 A) from (by
          unfold nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy141 r d) from (by
          unfold nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy162 A), (nb093AlphaDummy163 r d)), ((nb093AlphaDummy160 A),
        (nb093AlphaDummy161 r d)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy158 A),
        (nb093AlphaDummy159 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A) from (by
          unfold nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy141 r d) from (by
          unfold nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb093AlphaDummy136 A) ≠ (nb093AlphaDummy140 A) from (by
          unfold nb093AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0140 A) 0)))) (show (nb093AlphaDummy138 r d) ≠
        (nb093AlphaDummy141 r d) from (by
          unfold nb093AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0141 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy140 A), (nb093AlphaDummy141 r d)), ((nb093AlphaDummy136 A),
        (nb093AlphaDummy138 r d)), ((nb093AlphaDummy137 A), (nb093AlphaDummy139 r d)),
        ((nb093AlphaDummy162 A), (nb093AlphaDummy163 r d)), ((nb093AlphaDummy160 A),
        (nb093AlphaDummy161 r d)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy158 A),
        (nb093AlphaDummy159 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb093AlphaDummy160 A), (nb093AlphaDummy161 r d)),
                    ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                    ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                    ((nb093AlphaDummy158 A), (nb093AlphaDummy159 r d)),
                    ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                    ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                    ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                    ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                    ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb093_wpp_notmem_0422 (A : Class) :
    (nb093AlphaDummy000 A) ∉ ((synCfound)).fv := by
  simpa only [nb093AlphaDummy000, fv_syn_cfound] using (nb093_compact_fv_empty_0020 A)

theorem nb093_wpp_notmem_0423 (d : Var) : d ∉ ((synCfound)).fv := by
  simpa only [fv_syn_cfound] using (nb093_compact_fv_empty_0021 d)

theorem nb093_wpp_notmem_0424 (A : Class) :
    (nb093AlphaDummy001 A) ∉ ((synCfound)).fv := by
  simpa only [nb093AlphaDummy001, fv_syn_cfound] using (nb093_compact_fv_empty_0022 A)

theorem nb093_wpp_notmem_0425 (r : Var) : r ∉ ((synCfound)).fv := by
  simpa only [fv_syn_cfound] using (nb093_compact_fv_empty_0023 r)

theorem nb093_wpp_notmem_0426 (A : Class) :
    (nb093AlphaDummy006 A) ∉ ((synCfound)).fv := by
  simpa only [nb093AlphaDummy006, fv_syn_cfound] using (nb093_compact_fv_empty_0024 A)

theorem nb093_wpp_notmem_0427 (r : Var) (d : Var) :
    (nb093AlphaDummy007 r d) ∉ ((synCfound)).fv := by
  simpa only [nb093AlphaDummy007, fv_syn_cfound] using
    (nb093_compact_fv_empty_0025 r d)

theorem nb093_wpp_notmem_0428 (A : Class) :
    (nb093AlphaDummy004 A) ∉ ((synCfound)).fv := by
  simpa only [nb093AlphaDummy004, fv_syn_cfound] using (nb093_compact_fv_empty_0026 A)

theorem nb093_wpp_notmem_0429 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy005 A r d) ∉ ((synCfound)).fv := by
  simpa only [nb093AlphaDummy005, fv_syn_cfound] using
    (nb093_compact_fv_empty_0027 A r d)

theorem nb093_wpp_notmem_0430 (A : Class) :
    (nb093AlphaDummy002 A) ∉ ((synCfound)).fv := by
  simpa only [nb093AlphaDummy002, fv_syn_cfound] using (nb093_compact_fv_empty_0028 A)

theorem nb093_wpp_notmem_0431 (A : Class) (r : Var) (d : Var) :
    (nb093AlphaDummy003 A r d) ∉ ((synCfound)).fv := by
  simpa only [nb093AlphaDummy003, fv_syn_cfound] using
    (nb093_compact_fv_empty_0029 A r d)

theorem nb093_compact_envfresh_0029 (A : Class) (r : Var) (d : Var) :
    TEnvFresh
      [((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      ((synCfound)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb093AlphaDummy000 A) d (nb093_wpp_notmem_0422 A)
      (nb093_wpp_notmem_0423 d)
      (TEnvFresh.consFresh (nb093AlphaDummy001 A) r (nb093_wpp_notmem_0424 A)
        (nb093_wpp_notmem_0425 r)
        (TEnvFresh.consFresh (nb093AlphaDummy006 A) (nb093AlphaDummy007 r d)
          (nb093_wpp_notmem_0426 A) (nb093_wpp_notmem_0427 r d)
          (TEnvFresh.consFresh (nb093AlphaDummy004 A) (nb093AlphaDummy005 A r d)
            (nb093_wpp_notmem_0428 A) (nb093_wpp_notmem_0429 A r d)
            (TEnvFresh.consFresh (nb093AlphaDummy002 A) (nb093AlphaDummy003 A r d)
              (nb093_wpp_notmem_0430 A) (nb093_wpp_notmem_0431 A r d)
              (TEnvFresh.nil ((synCfound)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
