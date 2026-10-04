/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR093EnvironmentSupport


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

/-- Checked nominal proof certificate identified upstream as `nb093_wpp_refl_0029`. -/
@[expose]
noncomputable def nb093WppRefl0029 (A : Class) (r : Var) (d : Var) :
    TReflOn
      [((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      ((synCfound)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0029 A r d)

/-- Checked nominal proof certificate identified upstream as `nominal_df_lnpwc`. -/
@[expose]
noncomputable def nominalDfLnpwc (A : Class) (r : Var) (d : Var) (__dv_A_d : d ∉ A.fv)
    (__dv_A_r : r ∉ A.fv) (dv_d_r : d ≠ r) :
    Nominal.NPrf
      (.classEq (synClnpwc A) (synCin (synClntpc A) (synCopab r d
            (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                          ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                        (synClntpc A) (nb093WppRefl0000 A r d)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy006 A)
                                        from (by
                                          unfold nb093AlphaDummy006;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0002 A) 0))))) (Ne.symm
                                      (show d ≠ (nb093AlphaDummy007 r d) from (by
                                          unfold nb093AlphaDummy007;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0003 r d) 0)))))
                                    (TAlphaVar.there (Ne.symm (show (nb093AlphaDummy001 A) ≠
        (nb093AlphaDummy006 A) from (by
          unfold nb093AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0000 A) 0))))) (Ne.symm
                                        (show r ≠ (nb093AlphaDummy007 r d) from (by
          unfold nb093AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0001 r d) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.neg
                                      (nb093SplitAlpha0001 A r d dv_d_r)))))
                              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0007 A r d dv_d_r)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb093SplitAlpha0008 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb093SplitAlpha0008 A r d)))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb093AlphaDummy000 A), d),
                                    ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
                                      (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
                                      (nb093AlphaDummy005 A r d)),
                                    ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                                  (synCfound) (nb093WppRefl0029 A r d))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                          ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                        (synClntpc A) (nb093WppRefl0000 A r d)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb093AlphaDummy000 A) ≠ (nb093AlphaDummy006 A)
                                        from (by
                                          unfold nb093AlphaDummy006;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0002 A) 0))))) (Ne.symm
                                      (show d ≠ (nb093AlphaDummy007 r d) from (by
                                          unfold nb093AlphaDummy007;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0003 r d) 0)))))
                                    (TAlphaVar.there (Ne.symm (show (nb093AlphaDummy001 A) ≠
        (nb093AlphaDummy006 A) from (by
          unfold nb093AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0000 A) 0))))) (Ne.symm
                                        (show r ≠ (nb093AlphaDummy007 r d) from (by
          unfold nb093AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0001 r d) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.neg
                                      (nb093SplitAlpha0001 A r d dv_d_r)))))
                              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0007 A r d dv_d_r)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb093SplitAlpha0008 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb093SplitAlpha0008 A r d)))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb093AlphaDummy000 A), d),
                                    ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
                                      (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
                                      (nb093AlphaDummy005 A r d)),
                                    ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                                  (synCfound) (nb093WppRefl0029 A r d)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
