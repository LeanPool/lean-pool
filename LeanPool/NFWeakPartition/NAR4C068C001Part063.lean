/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block015

/-! NF weak partition development: NAR4C068C001Part063. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_en`. -/
@[expose]
noncomputable def nominalDfEn (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_f_y : f ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCen) (synCopab x y (synWex f (synWf1o (.cv f) (.cv x) (.cv y))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb068SplitAlpha0004 x y f dv_x_y) (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.neg (nb068SplitAlpha0192 x y f dv_f_x dv_f_y dv_x_y))
                  (TAlphaWff.conj (TAlphaWff.neg (nb068SplitAlpha0077 x y f dv_f_x dv_x_y))
                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                                  ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb068AlphaDummy284) ≠
        (nb068AlphaDummy288) from (by
          unfold
            nb068AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy290 f) from (by
          unfold
            nb068AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy287)
        from (by
          unfold
            nb068AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold
            nb068AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy293)
        from (by
          unfold
            nb068AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy294 f) from (by
          unfold
            nb068AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy291)
        from (by
          unfold
            nb068AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy292 f) from (by
          unfold
            nb068AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0085 x y f)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb068AlphaDummy284) ≠
        (nb068AlphaDummy288) from (by
          unfold
            nb068AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy290 f) from (by
          unfold
            nb068AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy287)
        from (by
          unfold
            nb068AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold
            nb068AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy293)
        from (by
          unfold
            nb068AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy294 f) from (by
          unfold
            nb068AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy291)
        from (by
          unfold
            nb068AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy292 f) from (by
          unfold
            nb068AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0085 x y f)))))))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb068SplitAlpha0088 x y f)))))))) (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy284) from
                                    (by
                                      unfold nb068AlphaDummy284;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0334)
                                              1)))) (show f ≠ (nb068AlphaDummy286 f) from (by
                                      unfold nb068AlphaDummy286;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0335 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy000) ≠ (nb068AlphaDummy283) from (by
                                        unfold nb068AlphaDummy283;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0334)
                                                0)))) (show f ≠ (nb068AlphaDummy285 f) from
                                      (by
                                        unfold nb068AlphaDummy285;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0335 f)
                                                0)))) (TAlphaVar.here _ _ _))))))))
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (Ne.symm dv_f_y) (TAlphaVar.here _ _ _)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
