/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block006

/-! NF weak partition development: NAR4C068C001Part023. -/


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
noncomputable def nb068_split_alpha_0031 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_233), (nb068_alpha_dummy_234 f)),
        ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
        ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_233))
          (Class.cab (nb068_alpha_dummy_203)
            (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_233))
            (Class.cab (nb068_alpha_dummy_203)
              (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_203))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_234 f))
          (Class.cab (nb068_alpha_dummy_205 f)
            (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_234 f))
            (Class.cab (nb068_alpha_dummy_205 f)
              (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_204) from
                    (by
                      unfold nb068_alpha_dummy_204;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
                  (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_206 f) from (by
                      unfold nb068_alpha_dummy_206;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_203) from
                      (by
                        unfold nb068_alpha_dummy_203;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 0))))
                    (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_205 f) from (by
                        unfold nb068_alpha_dummy_205;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0244 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_233) from (by
                          unfold nb068_alpha_dummy_233;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0246) 0))))
                      (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_234 f) from (by
                          unfold nb068_alpha_dummy_234;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0247 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_207) from (by
                            unfold nb068_alpha_dummy_207;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0243) 0))))
                        (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_208 f) from (by
                            unfold nb068_alpha_dummy_208;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0245 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068_alpha_dummy_000))).fv ∪
                              ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_047))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0030 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0030 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_235), (nb068_alpha_dummy_236 f)),
                          ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
                          ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
                          ((nb068_alpha_dummy_233), (nb068_alpha_dummy_234 f)),
                          ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
                          ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                          ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                          ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                          ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                          ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                          ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_204) from
                      (by
                        unfold nb068_alpha_dummy_204;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
                    (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_206 f) from (by
                        unfold nb068_alpha_dummy_206;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0244 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_203) from (by
                          unfold nb068_alpha_dummy_203;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0242) 0))))
                      (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_205 f) from (by
                          unfold nb068_alpha_dummy_205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0244 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_233) from (by
                            unfold nb068_alpha_dummy_233;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0246) 0))))
                        (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_234 f) from (by
                            unfold nb068_alpha_dummy_234;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0247 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_207) from (by
                              unfold nb068_alpha_dummy_207;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0243) 0))))
                          (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_208 f) from (by
                              unfold nb068_alpha_dummy_208;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0245 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb068_alpha_dummy_000))).fv ∪
                                ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_047))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0030 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0030 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_235), (nb068_alpha_dummy_236 f)),
                            ((nb068_alpha_dummy_204), (nb068_alpha_dummy_206 f)),
                            ((nb068_alpha_dummy_203), (nb068_alpha_dummy_205 f)),
                            ((nb068_alpha_dummy_233), (nb068_alpha_dummy_234 f)),
                            ((nb068_alpha_dummy_207), (nb068_alpha_dummy_208 f)),
                            ((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
                            ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
                            ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
                            ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
                            ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
                            ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0032 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_047), (nb068_alpha_dummy_050 f)),
        ((nb068_alpha_dummy_046), (nb068_alpha_dummy_049 f)),
        ((nb068_alpha_dummy_045), (nb068_alpha_dummy_048 f)),
        ((nb068_alpha_dummy_051), (nb068_alpha_dummy_052 f)),
        ((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (syn_wbr (Class.cv (nb068_alpha_dummy_045))
          (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_047)))
        (Wff.neg (syn_wbr (Class.cv (nb068_alpha_dummy_047)) (Class.cv (nb068_alpha_dummy_000))
            (Class.cv (nb068_alpha_dummy_046)))))
      (Wff.imp (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f))
          (Class.cv (nb068_alpha_dummy_050 f))) (Wff.neg
          (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f)
            (Class.cv (nb068_alpha_dummy_049 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_090) from
                                    (by
                                      unfold nb068_alpha_dummy_090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0084)
                                              1)))) (show
                                    (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_092 f) from
                                    (by
                                      unfold nb068_alpha_dummy_092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0086 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_089) from (by
                                        unfold nb068_alpha_dummy_089;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0084)
                                                0)))) (show (nb068_alpha_dummy_048 f) ≠
                                        (nb068_alpha_dummy_091 f) from (by
                                        unfold nb068_alpha_dummy_091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0086 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_095) from
                                        (by
                                          unfold nb068_alpha_dummy_095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0088)
                                                  0)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_096 f) from (by
                                          unfold nb068_alpha_dummy_096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0089 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠
        (nb068_alpha_dummy_093) from (by
          unfold nb068_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0085) 0)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_094 f) from (by
          unfold nb068_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0087 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv
        (Class.cv (nb068_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb068_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_047))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_050 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0011 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_090) from
                                    (by
                                      unfold nb068_alpha_dummy_090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0084)
                                              1)))) (show
                                    (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_092 f) from
                                    (by
                                      unfold nb068_alpha_dummy_092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0086 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_089) from (by
                                        unfold nb068_alpha_dummy_089;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0084)
                                                0)))) (show (nb068_alpha_dummy_048 f) ≠
                                        (nb068_alpha_dummy_091 f) from (by
                                        unfold nb068_alpha_dummy_091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0086 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_095) from
                                        (by
                                          unfold nb068_alpha_dummy_095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0088)
                                                  0)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_096 f) from (by
                                          unfold nb068_alpha_dummy_096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0089 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠
        (nb068_alpha_dummy_093) from (by
          unfold nb068_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0085) 0)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_094 f) from (by
          unfold nb068_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0087 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv
        (Class.cv (nb068_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb068_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_047))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_050 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0011 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0014 x y f))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0026 x y f)))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_204) from (by
                                        unfold nb068_alpha_dummy_204;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0214)
                                                1)))) (show (nb068_alpha_dummy_050 f) ≠
                                        (nb068_alpha_dummy_206 f) from (by
                                        unfold nb068_alpha_dummy_206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_203) from
                                        (by
                                          unfold nb068_alpha_dummy_203;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0214)
                                                  0)))) (show (nb068_alpha_dummy_050 f) ≠
        (nb068_alpha_dummy_205 f) from (by
                                          unfold nb068_alpha_dummy_205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_047) ≠
        (nb068_alpha_dummy_209) from (by
          unfold nb068_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0218) 0)))) (show (nb068_alpha_dummy_050 f) ≠
        (nb068_alpha_dummy_210 f) from (by
          unfold nb068_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_207) from (by
          unfold nb068_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0215) 0)))) (show (nb068_alpha_dummy_050 f) ≠
        (nb068_alpha_dummy_208 f) from (by
          unfold nb068_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_047))).fv ∪
                                        ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪
                                        ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0028 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_204) from (by
                                        unfold nb068_alpha_dummy_204;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0214)
                                                1)))) (show (nb068_alpha_dummy_050 f) ≠
                                        (nb068_alpha_dummy_206 f) from (by
                                        unfold nb068_alpha_dummy_206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_203) from
                                        (by
                                          unfold nb068_alpha_dummy_203;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0214)
                                                  0)))) (show (nb068_alpha_dummy_050 f) ≠
        (nb068_alpha_dummy_205 f) from (by
                                          unfold nb068_alpha_dummy_205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_047) ≠
        (nb068_alpha_dummy_209) from (by
          unfold nb068_alpha_dummy_209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0218) 0)))) (show (nb068_alpha_dummy_050 f) ≠
        (nb068_alpha_dummy_210 f) from (by
          unfold nb068_alpha_dummy_210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_047) ≠ (nb068_alpha_dummy_207) from (by
          unfold nb068_alpha_dummy_207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0215) 0)))) (show (nb068_alpha_dummy_050 f) ≠
        (nb068_alpha_dummy_208 f) from (by
          unfold nb068_alpha_dummy_208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_047))).fv ∪
                                        ((Class.cv (nb068_alpha_dummy_046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪
                                        ((Class.cv (nb068_alpha_dummy_049 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0028 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0031 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_047) from (by
                unfold nb068_alpha_dummy_047;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 2))))
            (show f ≠ (nb068_alpha_dummy_050 f) from (by
                unfold nb068_alpha_dummy_050;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 2))))
            (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_046) from (by
                  unfold nb068_alpha_dummy_046;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 1))))
              (show f ≠ (nb068_alpha_dummy_049 f) from (by
                  unfold nb068_alpha_dummy_049;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 1))))
              (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_045) from (by
                    unfold nb068_alpha_dummy_045;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 0))))
                (show f ≠ (nb068_alpha_dummy_048 f) from (by
                    unfold nb068_alpha_dummy_048;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_051) from
                    (by
                      unfold nb068_alpha_dummy_051;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0207) 0))))
                  (show f ≠ (nb068_alpha_dummy_052 f) from (by
                      unfold nb068_alpha_dummy_052;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0209 f) 0))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_043) from
                      (by
                        unfold nb068_alpha_dummy_043;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0204) 0))))
                    (show f ≠ (nb068_alpha_dummy_044 f) from (by
                        unfold nb068_alpha_dummy_044;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0205 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_041) from (by
                          unfold nb068_alpha_dummy_041;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0202) 0))))
                      (show f ≠ (nb068_alpha_dummy_042 f) from (by
                          unfold nb068_alpha_dummy_042;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0203 f) 0))))
                      (TAlphaVar.here _ _ _)))))))))))

theorem nb068_wpp_notmem_0596 : (nb068_alpha_dummy_043) ∉ ((syn_cid)).fv := by
  simpa only [nb068_alpha_dummy_043, fv_syn_cid] using (nb068_compact_fv_empty_0058)

theorem nb068_wpp_notmem_0597 (f : Var) : (nb068_alpha_dummy_044 f) ∉ ((syn_cid)).fv := by
  simpa only [nb068_alpha_dummy_044, fv_syn_cid] using (nb068_compact_fv_empty_0059 f)

theorem nb068_wpp_notmem_0598 : (nb068_alpha_dummy_041) ∉ ((syn_cid)).fv := by
  simpa only [nb068_alpha_dummy_041, fv_syn_cid] using (nb068_compact_fv_empty_0060)

theorem nb068_wpp_notmem_0599 (f : Var) : (nb068_alpha_dummy_042 f) ∉ ((syn_cid)).fv := by
  simpa only [nb068_alpha_dummy_042, fv_syn_cid] using (nb068_compact_fv_empty_0061 f)

theorem nb068_wpp_notmem_0600 : (nb068_alpha_dummy_000) ∉ ((syn_cid)).fv := by
  simpa only [nb068_alpha_dummy_000, fv_syn_cid] using (nb068_compact_fv_empty_0062)

theorem nb068_wpp_notmem_0601 (f : Var) : f ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb068_compact_fv_empty_0063 f)

theorem nb068_wpp_notmem_0602 : (nb068_alpha_dummy_002) ∉ ((syn_cid)).fv := by
  simpa only [nb068_alpha_dummy_002, fv_syn_cid] using (nb068_compact_fv_empty_0020)

theorem nb068_wpp_notmem_0603 (y : Var) : y ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb068_compact_fv_empty_0021 y)

theorem nb068_wpp_notmem_0604 : (nb068_alpha_dummy_001) ∉ ((syn_cid)).fv := by
  simpa only [nb068_alpha_dummy_001, fv_syn_cid] using (nb068_compact_fv_empty_0022)

theorem nb068_wpp_notmem_0605 (x : Var) : x ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb068_compact_fv_empty_0023 x)

theorem nb068_wpp_notmem_0606 : (nb068_alpha_dummy_003) ∉ ((syn_cid)).fv := by
  simpa only [nb068_alpha_dummy_003, fv_syn_cid] using (nb068_compact_fv_empty_0024)

theorem nb068_wpp_notmem_0607 (x : Var) (y : Var) (f : Var) :
    (nb068_alpha_dummy_004 x y f) ∉ ((syn_cid)).fv := by
  simpa only [nb068_alpha_dummy_004, fv_syn_cid] using (nb068_compact_fv_empty_0025 x y f)

theorem nb068_compact_envfresh_0042 (x : Var) (y : Var) (f : Var) :
    TEnvFresh
      [((nb068_alpha_dummy_043), (nb068_alpha_dummy_044 f)),
        ((nb068_alpha_dummy_041), (nb068_alpha_dummy_042 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      ((syn_cid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb068_alpha_dummy_043) (nb068_alpha_dummy_044 f)
      (nb068_wpp_notmem_0596) (nb068_wpp_notmem_0597 f)
      (TEnvFresh.consFresh (nb068_alpha_dummy_041) (nb068_alpha_dummy_042 f)
        (nb068_wpp_notmem_0598) (nb068_wpp_notmem_0599 f)
        (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0600)
          (nb068_wpp_notmem_0601 f)
          (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0602)
            (nb068_wpp_notmem_0603 y)
            (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0604)
              (nb068_wpp_notmem_0605 x)
              (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f)
                (nb068_wpp_notmem_0606) (nb068_wpp_notmem_0607 x y f)
                (TEnvFresh.nil ((syn_cid)).fv)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
