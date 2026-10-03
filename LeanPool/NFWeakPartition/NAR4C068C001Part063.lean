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

@[expose]
noncomputable def nominal_df_en (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_f_y : f ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cen) (syn_copab x y (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb068_split_alpha_0004 x y f dv_x_y) (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.neg (nb068_split_alpha_0192 x y f dv_f_x dv_f_y dv_x_y))
                  (TAlphaWff.conj (TAlphaWff.neg (nb068_split_alpha_0077 x y f dv_f_x dv_x_y))
                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                                  ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠
        (nb068_alpha_dummy_288) from (by
          unfold
            nb068_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_290 f) from (by
          unfold
            nb068_alpha_dummy_290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_287)
        from (by
          unfold
            nb068_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold
            nb068_alpha_dummy_289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_293)
        from (by
          unfold
            nb068_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_294 f) from (by
          unfold
            nb068_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_291)
        from (by
          unfold
            nb068_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_292 f) from (by
          unfold
            nb068_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0085 x y f)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠
        (nb068_alpha_dummy_288) from (by
          unfold
            nb068_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_290 f) from (by
          unfold
            nb068_alpha_dummy_290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_287)
        from (by
          unfold
            nb068_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold
            nb068_alpha_dummy_289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_293)
        from (by
          unfold
            nb068_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_294 f) from (by
          unfold
            nb068_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_291)
        from (by
          unfold
            nb068_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_292 f) from (by
          unfold
            nb068_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0085 x y f)))))))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb068_split_alpha_0088 x y f)))))))) (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_284) from
                                    (by
                                      unfold nb068_alpha_dummy_284;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0334)
                                              1)))) (show f ≠ (nb068_alpha_dummy_286 f) from (by
                                      unfold nb068_alpha_dummy_286;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0335 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_283) from (by
                                        unfold nb068_alpha_dummy_283;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0334)
                                                0)))) (show f ≠ (nb068_alpha_dummy_285 f) from
                                      (by
                                        unfold nb068_alpha_dummy_285;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0335 f)
                                                0)))) (TAlphaVar.here _ _ _))))))))
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (Ne.symm dv_f_y) (TAlphaVar.here _ _ _)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
