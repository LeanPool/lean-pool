/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C067C001Part021Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part021`. -/


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

@[expose]
noncomputable def nb067_wpp_refl_0050 (x : Var) (y : Var) (f : Var) :
    TReflOn
      [((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0050 x y f)

@[expose]
noncomputable def nb067_split_alpha_0038 (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Class.cab (nb067_alpha_dummy_081) (syn_wnan
          (Wff.classMem (Class.cv (nb067_alpha_dummy_081))
            (syn_ccom (Class.cv (nb067_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))))
          (Wff.classMem (Class.cv (nb067_alpha_dummy_081)) (syn_cid))))
      (Class.cab (nb067_alpha_dummy_082 f) (syn_wnan
          (Wff.classMem (Class.cv (nb067_alpha_dummy_082 f))
            (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))))
          (Wff.classMem (Class.cv (nb067_alpha_dummy_082 f)) (syn_cid)))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (Ne.symm
                          (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_089) from (by
                              unfold nb067_alpha_dummy_089;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0094) 0))))) (Ne.symm
                          (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_090 f) from (by
                              unfold nb067_alpha_dummy_090;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0095 f) 0)))))
                        (TAlphaVar.there (Ne.symm
                            (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_089) from (by
                                unfold nb067_alpha_dummy_089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0092) 0))))) (Ne.symm
                            (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_090 f) from (by
                                unfold nb067_alpha_dummy_090;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0093 f) 0)))))
                          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_092) from (by
          unfold nb067_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 1)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_094 f) from (by
          unfold nb067_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f)
                  1)))) (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_091)
        from (by
          unfold nb067_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096)
                  0)))) (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_093 f) from (by
          unfold nb067_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_097)
        from (by
          unfold nb067_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0100)
                  0)))) (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_098 f) from (by
          unfold nb067_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0101 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_095)
        from (by
          unfold nb067_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0097)
                  0)))) (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_096 f) from (by
          unfold nb067_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb067_split_alpha_0011 x y f))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_092) from (by
          unfold nb067_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 1)))) (show (nb067_alpha_dummy_086 f) ≠
        (nb067_alpha_dummy_094 f) from (by
          unfold nb067_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f)
                  1)))) (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_091)
        from (by
          unfold nb067_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096)
                  0)))) (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_093 f) from (by
          unfold nb067_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_097)
        from (by
          unfold nb067_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0100)
                  0)))) (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_098 f) from (by
          unfold nb067_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0101 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_095)
        from (by
          unfold nb067_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0097)
                  0)))) (show (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_096 f) from (by
          unfold nb067_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb067_split_alpha_0011 x y f)))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb067_split_alpha_0014 x y f)))))))))
                  (TAlphaWff.ex (TAlphaWff.neg (nb067_split_alpha_0037 x y f))))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn
            [((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
              ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
              ((nb067_alpha_dummy_000), f),
              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
            (syn_cid) (nb067_wpp_refl_0050 x y f))))))

@[expose]
noncomputable def nb067_split_alpha_0039 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
        ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
        ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
        ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
        ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
        ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
        ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
        ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
        ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_105))
            (syn_cun (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_108 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_109 f))
              (Class.cv (nb067_alpha_dummy_110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_113) from (by
                              unfold nb067_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0110) 0))))
                          (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_114 f) from (by
                              unfold nb067_alpha_dummy_114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0111 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_111) from (by
                                unfold nb067_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0108) 0))))
                            (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_112 f) from (by
                                unfold nb067_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0109 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_113) from (by
                              unfold nb067_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0114) 0))))
                          (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_114 f) from (by
                              unfold nb067_alpha_dummy_114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0115 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_111) from (by
                                unfold nb067_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0112) 0))))
                            (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_112 f) from (by
                                unfold nb067_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0113 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_113) from (by
                              unfold nb067_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0110) 0))))
                          (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_114 f) from (by
                              unfold nb067_alpha_dummy_114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0111 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_111) from (by
                                unfold nb067_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0108) 0))))
                            (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_112 f) from (by
                                unfold nb067_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0109 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_113) from (by
                              unfold nb067_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0114) 0))))
                          (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_114 f) from (by
                              unfold nb067_alpha_dummy_114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0115 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_111) from (by
                                unfold nb067_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0112) 0))))
                            (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_112 f) from (by
                                unfold nb067_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0113 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
          ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
          ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
          ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
          ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
          ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
          ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
          ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
          ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
          ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_117) from (by
                                unfold nb067_alpha_dummy_117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0118) 0))))
                            (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_118 f) from (by
                                unfold nb067_alpha_dummy_118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0119 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_115) from (by
                                  unfold nb067_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0116) 0))))
                              (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_116 f) from
                                (by
                                  unfold nb067_alpha_dummy_116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0117 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_117) from (by
                                unfold nb067_alpha_dummy_117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0118) 0))))
                            (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_118 f) from (by
                                unfold nb067_alpha_dummy_118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0119 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_115) from (by
                                  unfold nb067_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0116) 0))))
                              (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_116 f) from
                                (by
                                  unfold nb067_alpha_dummy_116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0117 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_119) from (by
                                unfold nb067_alpha_dummy_119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0122) 0))))
                            (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_120 f) from (by
                                unfold nb067_alpha_dummy_120;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0123 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_115) from (by
                                  unfold nb067_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0120) 0))))
                              (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_116 f) from
                                (by
                                  unfold nb067_alpha_dummy_116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0121 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_119) from (by
                                unfold nb067_alpha_dummy_119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0122) 0))))
                            (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_120 f) from (by
                                unfold nb067_alpha_dummy_120;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0123 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_115) from (by
                                  unfold nb067_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0120) 0))))
                              (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_116 f) from
                                (by
                                  unfold nb067_alpha_dummy_116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0121 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0040 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
        ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
        ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
        (syn_cphi (Class.cv (nb067_alpha_dummy_092))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
        (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
            ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067_alpha_dummy_092) ≠ (nb067_alpha_dummy_099) from (by
                    unfold nb067_alpha_dummy_099;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 0))))
                (show (nb067_alpha_dummy_094 f) ≠ (nb067_alpha_dummy_101 f) from (by
                    unfold nb067_alpha_dummy_101;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 0))))
                (TAlphaVar.there (show (nb067_alpha_dummy_092) ≠ (nb067_alpha_dummy_100) from
                    (by
                      unfold nb067_alpha_dummy_100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 1))))
                  (show (nb067_alpha_dummy_094 f) ≠ (nb067_alpha_dummy_102 f) from (by
                      unfold nb067_alpha_dummy_102;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb067_alpha_dummy_092))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb067_alpha_dummy_094 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_106) from
                                    (by
                                      unfold nb067_alpha_dummy_106;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0106)
                                              1)))) (show
                                    (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_109 f) from
                                    (by
                                      unfold nb067_alpha_dummy_109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0107 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_105) from (by
                                        unfold nb067_alpha_dummy_105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0106)
                                                0)))) (show (nb067_alpha_dummy_101 f) ≠
                                        (nb067_alpha_dummy_108 f) from (by
                                        unfold nb067_alpha_dummy_108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0107 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_103) from
                                        (by
                                          unfold nb067_alpha_dummy_103;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0104)
                                                  0)))) (show (nb067_alpha_dummy_101 f) ≠
        (nb067_alpha_dummy_104 f) from (by
                                          unfold nb067_alpha_dummy_104;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0105 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
                                      ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
                                      ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
                                      ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                                      ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                                      ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                                      ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                                      ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                                      ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
                                      ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                      ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                        (nb067_alpha_dummy_004 x y f)),
                                      ((nb067_alpha_dummy_002), y),
                                      ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005),
                                        (nb067_alpha_dummy_006 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb067_split_alpha_0039 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_103) from (by
                              unfold nb067_alpha_dummy_103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                          (show (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_104 f) from (by
                              unfold nb067_alpha_dummy_104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                          ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                          ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                          ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                          ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                          ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
                          ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_103) from (by
                            unfold nb067_alpha_dummy_103;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                        (show (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_104 f) from (by
                            unfold nb067_alpha_dummy_104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_103) from (by
                              unfold nb067_alpha_dummy_103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                          (show (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_104 f) from (by
                              unfold nb067_alpha_dummy_104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                          ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                          ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                          ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                          ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                          ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
                          ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part022`. -/


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

@[expose]
noncomputable def nb067_split_alpha_0041 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
        ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
        ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
        ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
        ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
        ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
        ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
        ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
        ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
        ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
        ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_105))
            (syn_cun (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_108 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_109 f))
              (Class.cv (nb067_alpha_dummy_110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_113) from (by
                              unfold nb067_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0110) 0))))
                          (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_114 f) from (by
                              unfold nb067_alpha_dummy_114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0111 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_111) from (by
                                unfold nb067_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0108) 0))))
                            (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_112 f) from (by
                                unfold nb067_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0109 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_113) from (by
                              unfold nb067_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0114) 0))))
                          (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_114 f) from (by
                              unfold nb067_alpha_dummy_114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0115 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_111) from (by
                                unfold nb067_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0112) 0))))
                            (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_112 f) from (by
                                unfold nb067_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0113 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_113) from (by
                              unfold nb067_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0110) 0))))
                          (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_114 f) from (by
                              unfold nb067_alpha_dummy_114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0111 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_111) from (by
                                unfold nb067_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0108) 0))))
                            (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_112 f) from (by
                                unfold nb067_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0109 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_113) from (by
                              unfold nb067_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0114) 0))))
                          (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_114 f) from (by
                              unfold nb067_alpha_dummy_114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0115 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_111) from (by
                                unfold nb067_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0112) 0))))
                            (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_112 f) from (by
                                unfold nb067_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0113 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
          ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
          ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
          ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
          ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
          ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
          ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
          ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
          ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
          ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
          ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
          ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_117) from (by
                                unfold nb067_alpha_dummy_117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0118) 0))))
                            (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_118 f) from (by
                                unfold nb067_alpha_dummy_118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0119 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_115) from (by
                                  unfold nb067_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0116) 0))))
                              (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_116 f) from
                                (by
                                  unfold nb067_alpha_dummy_116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0117 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_117) from (by
                                unfold nb067_alpha_dummy_117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0118) 0))))
                            (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_118 f) from (by
                                unfold nb067_alpha_dummy_118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0119 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_115) from (by
                                  unfold nb067_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0116) 0))))
                              (show (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_116 f) from
                                (by
                                  unfold nb067_alpha_dummy_116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0117 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_119) from (by
                                unfold nb067_alpha_dummy_119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0122) 0))))
                            (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_120 f) from (by
                                unfold nb067_alpha_dummy_120;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0123 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_115) from (by
                                  unfold nb067_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0120) 0))))
                              (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_116 f) from
                                (by
                                  unfold nb067_alpha_dummy_116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0121 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_119) from (by
                                unfold nb067_alpha_dummy_119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0122) 0))))
                            (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_120 f) from (by
                                unfold nb067_alpha_dummy_120;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0123 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_107) ≠ (nb067_alpha_dummy_115) from (by
                                  unfold nb067_alpha_dummy_115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0120) 0))))
                              (show (nb067_alpha_dummy_110 f) ≠ (nb067_alpha_dummy_116 f) from
                                (by
                                  unfold nb067_alpha_dummy_116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0121 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0042 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
        ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
        ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
        ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
        ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
        ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
        ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_099))
          (Class.cv (nb067_alpha_dummy_092))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_100))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_099))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_101 f))
          (Class.cv (nb067_alpha_dummy_094 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_102 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_101 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_092) ≠ (nb067_alpha_dummy_099) from (by
              unfold nb067_alpha_dummy_099;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 0))))
          (show (nb067_alpha_dummy_094 f) ≠ (nb067_alpha_dummy_101 f) from (by
              unfold nb067_alpha_dummy_101;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_092) ≠ (nb067_alpha_dummy_100) from (by
                unfold nb067_alpha_dummy_100;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 1))))
            (show (nb067_alpha_dummy_094 f) ≠ (nb067_alpha_dummy_102 f) from (by
                unfold nb067_alpha_dummy_102;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 1))))
            (TAlphaVar.there (show (nb067_alpha_dummy_092) ≠ (nb067_alpha_dummy_125) from (by
                  unfold nb067_alpha_dummy_125;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0132) 0))))
              (show (nb067_alpha_dummy_094 f) ≠ (nb067_alpha_dummy_126 f) from (by
                  unfold nb067_alpha_dummy_126;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0133 f) 0))))
              (TAlphaVar.there (show (nb067_alpha_dummy_092) ≠ (nb067_alpha_dummy_123) from (by
                    unfold nb067_alpha_dummy_123;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0130) 0))))
                (show (nb067_alpha_dummy_094 f) ≠ (nb067_alpha_dummy_124 f) from (by
                    unfold nb067_alpha_dummy_124;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0131 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_092))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_094 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_106) from (by
                                  unfold nb067_alpha_dummy_106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0106) 1))))
                              (show (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_109 f) from
                                (by
                                  unfold nb067_alpha_dummy_109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0107 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_105) from (by
                                    unfold nb067_alpha_dummy_105;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0106) 0)))) (show
                                  (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_108 f) from (by
                                    unfold nb067_alpha_dummy_108;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0107 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_103) from
                                    (by
                                      unfold nb067_alpha_dummy_103;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0104)
                                              0)))) (show
                                    (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_104 f) from
                                    (by
                                      unfold nb067_alpha_dummy_104;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0105 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
                                  ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
                                  ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
                                  ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                                  ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                                  ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                                  ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
                                  ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                                  ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                                  ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                                  ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                                  ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0041 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_103) from (by
                          unfold nb067_alpha_dummy_103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                      (show (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_104 f) from (by
                          unfold nb067_alpha_dummy_104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                      ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                      ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                      ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
                      ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                      ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                      ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                      ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                      ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_103) from
                      (by
                        unfold nb067_alpha_dummy_103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                    (show (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_104 f) from (by
                        unfold nb067_alpha_dummy_104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_103) from (by
                          unfold nb067_alpha_dummy_103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                      (show (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_104 f) from (by
                          unfold nb067_alpha_dummy_104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                      ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                      ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                      ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
                      ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                      ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                      ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                      ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                      ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0043 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_121))
          (Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_121))
            (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_122 f))
          (Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_122 f))
            (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_092) from
                    (by
                      unfold nb067_alpha_dummy_092;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))))
                  (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_094 f) from (by
                      unfold nb067_alpha_dummy_094;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_091) from
                      (by
                        unfold nb067_alpha_dummy_091;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))))
                    (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_093 f) from (by
                        unfold nb067_alpha_dummy_093;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0126 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_121) from (by
                          unfold nb067_alpha_dummy_121;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0128) 0))))
                      (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_122 f) from (by
                          unfold nb067_alpha_dummy_122;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0129 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_095) from (by
                            unfold nb067_alpha_dummy_095;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0125) 0))))
                        (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_096 f) from (by
                            unfold nb067_alpha_dummy_096;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0127 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0042 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0042 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                          ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                          ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                          ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                          ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_092) from
                      (by
                        unfold nb067_alpha_dummy_092;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))))
                    (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_094 f) from (by
                        unfold nb067_alpha_dummy_094;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0126 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_091) from (by
                          unfold nb067_alpha_dummy_091;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0124) 0))))
                      (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_093 f) from (by
                          unfold nb067_alpha_dummy_093;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0126 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_121) from (by
                            unfold nb067_alpha_dummy_121;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0128) 0))))
                        (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_122 f) from (by
                            unfold nb067_alpha_dummy_122;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0129 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_095) from (by
                              unfold nb067_alpha_dummy_095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0125) 0))))
                          (show (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_096 f) from (by
                              unfold nb067_alpha_dummy_096;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0127 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0042 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0042 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                            ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                            ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                            ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                            ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                            ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                            ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                            ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0044 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
        ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
        ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
        ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
        ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
        ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
        ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
        ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
        ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_141))
            (syn_cun (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_144 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_145 f))
              (Class.cv (nb067_alpha_dummy_146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_149) from (by
                              unfold nb067_alpha_dummy_149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0148) 0))))
                          (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_150 f) from (by
                              unfold nb067_alpha_dummy_150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0149 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_147) from (by
                                unfold nb067_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0146) 0))))
                            (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_148 f) from (by
                                unfold nb067_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0147 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_149) from (by
                              unfold nb067_alpha_dummy_149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0152) 0))))
                          (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_150 f) from (by
                              unfold nb067_alpha_dummy_150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0153 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_147) from (by
                                unfold nb067_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0150) 0))))
                            (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_148 f) from (by
                                unfold nb067_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0151 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_149) from (by
                              unfold nb067_alpha_dummy_149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0148) 0))))
                          (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_150 f) from (by
                              unfold nb067_alpha_dummy_150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0149 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_147) from (by
                                unfold nb067_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0146) 0))))
                            (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_148 f) from (by
                                unfold nb067_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0147 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_149) from (by
                              unfold nb067_alpha_dummy_149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0152) 0))))
                          (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_150 f) from (by
                              unfold nb067_alpha_dummy_150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0153 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_147) from (by
                                unfold nb067_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0150) 0))))
                            (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_148 f) from (by
                                unfold nb067_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0151 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
          ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
          ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
          ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
          ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
          ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
          ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
          ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
          ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
          ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_153) from (by
                                unfold nb067_alpha_dummy_153;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0156) 0))))
                            (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_154 f) from (by
                                unfold nb067_alpha_dummy_154;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0157 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_151) from (by
                                  unfold nb067_alpha_dummy_151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0154) 0))))
                              (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_152 f) from
                                (by
                                  unfold nb067_alpha_dummy_152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0155 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_153) from (by
                                unfold nb067_alpha_dummy_153;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0156) 0))))
                            (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_154 f) from (by
                                unfold nb067_alpha_dummy_154;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0157 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_151) from (by
                                  unfold nb067_alpha_dummy_151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0154) 0))))
                              (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_152 f) from
                                (by
                                  unfold nb067_alpha_dummy_152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0155 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_155) from (by
                                unfold nb067_alpha_dummy_155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0160) 0))))
                            (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_156 f) from (by
                                unfold nb067_alpha_dummy_156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0161 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_151) from (by
                                  unfold nb067_alpha_dummy_151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0158) 0))))
                              (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_152 f) from
                                (by
                                  unfold nb067_alpha_dummy_152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0159 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_155) from (by
                                unfold nb067_alpha_dummy_155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0160) 0))))
                            (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_156 f) from (by
                                unfold nb067_alpha_dummy_156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0161 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_151) from (by
                                  unfold nb067_alpha_dummy_151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0158) 0))))
                              (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_152 f) from
                                (by
                                  unfold nb067_alpha_dummy_152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0159 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part023`. -/


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

@[expose]
noncomputable def nb067_split_alpha_0045 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
        ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
        ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
        ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
        ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_135))
            (Class.cv (nb067_alpha_dummy_128))) (Wff.classEq (Class.cv (nb067_alpha_dummy_136))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_135))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_137 f))
            (Class.cv (nb067_alpha_dummy_130 f)))
          (Wff.classEq (Class.cv (nb067_alpha_dummy_138 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_137 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067_alpha_dummy_128) ≠ (nb067_alpha_dummy_135) from (by
                unfold nb067_alpha_dummy_135;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 0))))
            (show (nb067_alpha_dummy_130 f) ≠ (nb067_alpha_dummy_137 f) from (by
                unfold nb067_alpha_dummy_137;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 0))))
            (TAlphaVar.there (show (nb067_alpha_dummy_128) ≠ (nb067_alpha_dummy_136) from (by
                  unfold nb067_alpha_dummy_136;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 1))))
              (show (nb067_alpha_dummy_130 f) ≠ (nb067_alpha_dummy_138 f) from (by
                  unfold nb067_alpha_dummy_138;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_128))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_130 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_142) from (by
                                  unfold nb067_alpha_dummy_142;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0144) 1))))
                              (show (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_145 f) from
                                (by
                                  unfold nb067_alpha_dummy_145;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0145 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_141) from (by
                                    unfold nb067_alpha_dummy_141;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0144) 0)))) (show
                                  (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_144 f) from (by
                                    unfold nb067_alpha_dummy_144;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0145 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_139) from
                                    (by
                                      unfold nb067_alpha_dummy_139;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0142)
                                              0)))) (show
                                    (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_140 f) from
                                    (by
                                      unfold nb067_alpha_dummy_140;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0143 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
                                  ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
                                  ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
                                  ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                                  ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                                  ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                                  ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                                  ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                                  ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
                                  ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0044 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_139) from (by
                          unfold nb067_alpha_dummy_139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                      (show (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_140 f) from (by
                          unfold nb067_alpha_dummy_140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                      ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                      ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                      ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                      ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                      ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
                      ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_139) from
                      (by
                        unfold nb067_alpha_dummy_139;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                    (show (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_140 f) from (by
                        unfold nb067_alpha_dummy_140;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_139) from (by
                          unfold nb067_alpha_dummy_139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                      (show (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_140 f) from (by
                          unfold nb067_alpha_dummy_140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                      ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                      ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                      ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                      ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                      ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
                      ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0046 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
        ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
        ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
        ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
        ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
        ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
        ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
        ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
        ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
        ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
        ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_141))
            (syn_cun (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_144 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_145 f))
              (Class.cv (nb067_alpha_dummy_146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_149) from (by
                              unfold nb067_alpha_dummy_149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0148) 0))))
                          (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_150 f) from (by
                              unfold nb067_alpha_dummy_150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0149 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_147) from (by
                                unfold nb067_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0146) 0))))
                            (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_148 f) from (by
                                unfold nb067_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0147 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_149) from (by
                              unfold nb067_alpha_dummy_149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0152) 0))))
                          (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_150 f) from (by
                              unfold nb067_alpha_dummy_150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0153 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_147) from (by
                                unfold nb067_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0150) 0))))
                            (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_148 f) from (by
                                unfold nb067_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0151 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_149) from (by
                              unfold nb067_alpha_dummy_149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0148) 0))))
                          (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_150 f) from (by
                              unfold nb067_alpha_dummy_150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0149 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_147) from (by
                                unfold nb067_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0146) 0))))
                            (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_148 f) from (by
                                unfold nb067_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0147 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_149) from (by
                              unfold nb067_alpha_dummy_149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0152) 0))))
                          (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_150 f) from (by
                              unfold nb067_alpha_dummy_150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0153 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_147) from (by
                                unfold nb067_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0150) 0))))
                            (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_148 f) from (by
                                unfold nb067_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0151 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
          ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
          ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
          ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
          ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
          ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
          ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
          ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
          ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
          ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
          ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
          ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_153) from (by
                                unfold nb067_alpha_dummy_153;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0156) 0))))
                            (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_154 f) from (by
                                unfold nb067_alpha_dummy_154;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0157 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_151) from (by
                                  unfold nb067_alpha_dummy_151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0154) 0))))
                              (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_152 f) from
                                (by
                                  unfold nb067_alpha_dummy_152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0155 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_153) from (by
                                unfold nb067_alpha_dummy_153;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0156) 0))))
                            (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_154 f) from (by
                                unfold nb067_alpha_dummy_154;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0157 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_151) from (by
                                  unfold nb067_alpha_dummy_151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0154) 0))))
                              (show (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_152 f) from
                                (by
                                  unfold nb067_alpha_dummy_152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0155 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_155) from (by
                                unfold nb067_alpha_dummy_155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0160) 0))))
                            (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_156 f) from (by
                                unfold nb067_alpha_dummy_156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0161 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_151) from (by
                                  unfold nb067_alpha_dummy_151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0158) 0))))
                              (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_152 f) from
                                (by
                                  unfold nb067_alpha_dummy_152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0159 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_155) from (by
                                unfold nb067_alpha_dummy_155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0160) 0))))
                            (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_156 f) from (by
                                unfold nb067_alpha_dummy_156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0161 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_143) ≠ (nb067_alpha_dummy_151) from (by
                                  unfold nb067_alpha_dummy_151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0158) 0))))
                              (show (nb067_alpha_dummy_146 f) ≠ (nb067_alpha_dummy_152 f) from
                                (by
                                  unfold nb067_alpha_dummy_152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0159 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0047 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
        ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
        ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
        ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
        ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
        ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
        ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_135))
          (Class.cv (nb067_alpha_dummy_128))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_136))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_135))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_137 f))
          (Class.cv (nb067_alpha_dummy_130 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_138 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_137 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_128) ≠ (nb067_alpha_dummy_135) from (by
              unfold nb067_alpha_dummy_135;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 0))))
          (show (nb067_alpha_dummy_130 f) ≠ (nb067_alpha_dummy_137 f) from (by
              unfold nb067_alpha_dummy_137;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_128) ≠ (nb067_alpha_dummy_136) from (by
                unfold nb067_alpha_dummy_136;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 1))))
            (show (nb067_alpha_dummy_130 f) ≠ (nb067_alpha_dummy_138 f) from (by
                unfold nb067_alpha_dummy_138;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 1))))
            (TAlphaVar.there (show (nb067_alpha_dummy_128) ≠ (nb067_alpha_dummy_161) from (by
                  unfold nb067_alpha_dummy_161;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0170) 0))))
              (show (nb067_alpha_dummy_130 f) ≠ (nb067_alpha_dummy_162 f) from (by
                  unfold nb067_alpha_dummy_162;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0171 f) 0))))
              (TAlphaVar.there (show (nb067_alpha_dummy_128) ≠ (nb067_alpha_dummy_159) from (by
                    unfold nb067_alpha_dummy_159;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0168) 0))))
                (show (nb067_alpha_dummy_130 f) ≠ (nb067_alpha_dummy_160 f) from (by
                    unfold nb067_alpha_dummy_160;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0169 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_128))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_130 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_142) from (by
                                  unfold nb067_alpha_dummy_142;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0144) 1))))
                              (show (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_145 f) from
                                (by
                                  unfold nb067_alpha_dummy_145;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0145 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_141) from (by
                                    unfold nb067_alpha_dummy_141;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0144) 0)))) (show
                                  (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_144 f) from (by
                                    unfold nb067_alpha_dummy_144;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0145 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_139) from
                                    (by
                                      unfold nb067_alpha_dummy_139;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0142)
                                              0)))) (show
                                    (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_140 f) from
                                    (by
                                      unfold nb067_alpha_dummy_140;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0143 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
                                  ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
                                  ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
                                  ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                                  ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                                  ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                                  ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
                                  ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                                  ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                                  ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                                  ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                                  ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0046 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_139) from (by
                          unfold nb067_alpha_dummy_139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                      (show (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_140 f) from (by
                          unfold nb067_alpha_dummy_140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                      ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                      ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                      ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
                      ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                      ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                      ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                      ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                      ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_139) from
                      (by
                        unfold nb067_alpha_dummy_139;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                    (show (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_140 f) from (by
                        unfold nb067_alpha_dummy_140;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_139) from (by
                          unfold nb067_alpha_dummy_139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                      (show (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_140 f) from (by
                          unfold nb067_alpha_dummy_140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                      ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                      ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                      ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
                      ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                      ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                      ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                      ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                      ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0048 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_157))
          (Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_157))
            (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_158 f))
          (Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_158 f))
            (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_128) from
                    (by
                      unfold nb067_alpha_dummy_128;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))))
                  (show (nb067_alpha_dummy_088 f) ≠ (nb067_alpha_dummy_130 f) from (by
                      unfold nb067_alpha_dummy_130;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_127) from
                      (by
                        unfold nb067_alpha_dummy_127;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))))
                    (show (nb067_alpha_dummy_088 f) ≠ (nb067_alpha_dummy_129 f) from (by
                        unfold nb067_alpha_dummy_129;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0164 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_157) from (by
                          unfold nb067_alpha_dummy_157;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0166) 0))))
                      (show (nb067_alpha_dummy_088 f) ≠ (nb067_alpha_dummy_158 f) from (by
                          unfold nb067_alpha_dummy_158;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0167 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_131) from (by
                            unfold nb067_alpha_dummy_131;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0163) 0))))
                        (show (nb067_alpha_dummy_088 f) ≠ (nb067_alpha_dummy_132 f) from (by
                            unfold nb067_alpha_dummy_132;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0165 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_085))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_088 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0047 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0047 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                          ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                          ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                          ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                          ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_128) from
                      (by
                        unfold nb067_alpha_dummy_128;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))))
                    (show (nb067_alpha_dummy_088 f) ≠ (nb067_alpha_dummy_130 f) from (by
                        unfold nb067_alpha_dummy_130;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0164 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_127) from (by
                          unfold nb067_alpha_dummy_127;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0162) 0))))
                      (show (nb067_alpha_dummy_088 f) ≠ (nb067_alpha_dummy_129 f) from (by
                          unfold nb067_alpha_dummy_129;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0164 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_157) from (by
                            unfold nb067_alpha_dummy_157;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0166) 0))))
                        (show (nb067_alpha_dummy_088 f) ≠ (nb067_alpha_dummy_158 f) from (by
                            unfold nb067_alpha_dummy_158;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0167 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_085) ≠ (nb067_alpha_dummy_131) from (by
                              unfold nb067_alpha_dummy_131;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0163) 0))))
                          (show (nb067_alpha_dummy_088 f) ≠ (nb067_alpha_dummy_132 f) from (by
                              unfold nb067_alpha_dummy_132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0165 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_085))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_088 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0047 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0047 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                            ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                            ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                            ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                            ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                            ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                            ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                            ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                            ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part024`. -/


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

@[expose]
noncomputable def nb067_split_alpha_0049 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
        ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
        ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
        ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
        ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_183))
            (syn_cun (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_186 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_187 f))
              (Class.cv (nb067_alpha_dummy_188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
          ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
          ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
          ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
          ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
          ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
          ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_195) from (by
                                unfold nb067_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_196 f) from (by
                                unfold nb067_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_195) from (by
                                unfold nb067_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_196 f) from (by
                                unfold nb067_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_197) from (by
                                unfold nb067_alpha_dummy_197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_198 f) from (by
                                unfold nb067_alpha_dummy_198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_197) from (by
                                unfold nb067_alpha_dummy_197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_198 f) from (by
                                unfold nb067_alpha_dummy_198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0050 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_177))
          (Class.cv (nb067_alpha_dummy_170))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_178))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_177))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f))
          (Class.cv (nb067_alpha_dummy_172 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_180 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_179 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_177) from (by
              unfold nb067_alpha_dummy_177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0))))
          (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_179 f) from (by
              unfold nb067_alpha_dummy_179;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_178) from (by
                unfold nb067_alpha_dummy_178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1))))
            (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_180 f) from (by
                unfold nb067_alpha_dummy_180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_184) from (by
                                  unfold nb067_alpha_dummy_184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0186) 1))))
                              (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_187 f) from
                                (by
                                  unfold nb067_alpha_dummy_187;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0187 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_183) from (by
                                    unfold nb067_alpha_dummy_183;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0186) 0)))) (show
                                  (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_186 f) from (by
                                    unfold nb067_alpha_dummy_186;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0187 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from
                                    (by
                                      unfold nb067_alpha_dummy_181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0184)
                                              0)))) (show
                                    (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from
                                    (by
                                      unfold nb067_alpha_dummy_182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0185 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
                                  ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
                                  ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
                                  ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                                  ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                                  ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                                  ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                                  ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                                  ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
                                  ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0049 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from (by
                          unfold nb067_alpha_dummy_181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                          unfold nb067_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                      ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                      ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                      ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                      ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                      ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
                      ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                      ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                      ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                      ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from
                      (by
                        unfold nb067_alpha_dummy_181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                    (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                        unfold nb067_alpha_dummy_182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from (by
                          unfold nb067_alpha_dummy_181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                          unfold nb067_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                      ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                      ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                      ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                      ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                      ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
                      ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                      ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                      ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                      ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0051 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
        ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
        ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
        ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
        ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
        ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_183))
            (syn_cun (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_186 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_187 f))
              (Class.cv (nb067_alpha_dummy_188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_191) from (by
                              unfold nb067_alpha_dummy_191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_192 f) from (by
                              unfold nb067_alpha_dummy_192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_189) from (by
                                unfold nb067_alpha_dummy_189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_190 f) from (by
                                unfold nb067_alpha_dummy_190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
          ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
          ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
          ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
          ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
          ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
          ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
          ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
          ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_195) from (by
                                unfold nb067_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_196 f) from (by
                                unfold nb067_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_195) from (by
                                unfold nb067_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_196 f) from (by
                                unfold nb067_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_197) from (by
                                unfold nb067_alpha_dummy_197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_198 f) from (by
                                unfold nb067_alpha_dummy_198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_197) from (by
                                unfold nb067_alpha_dummy_197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_198 f) from (by
                                unfold nb067_alpha_dummy_198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_185) ≠ (nb067_alpha_dummy_193) from (by
                                  unfold nb067_alpha_dummy_193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067_alpha_dummy_188 f) ≠ (nb067_alpha_dummy_194 f) from
                                (by
                                  unfold nb067_alpha_dummy_194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0052 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
        ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_178))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_177))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_180 f))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_179 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_184) from (by
                              unfold nb067_alpha_dummy_184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0186) 1))))
                          (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_187 f) from (by
                              unfold nb067_alpha_dummy_187;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0187 f) 1))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_183) from (by
                                unfold nb067_alpha_dummy_183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0186) 0))))
                            (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_186 f) from (by
                                unfold nb067_alpha_dummy_186;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from (by
                                  unfold nb067_alpha_dummy_181;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                              (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from
                                (by
                                  unfold nb067_alpha_dummy_182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
                              ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
                              ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
                              ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                              ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                              ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                              ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
                              ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                              ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                              ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                              ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                              ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                              ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                              ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                              ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                              ((nb067_alpha_dummy_000), f),
                              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067_split_alpha_0051 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from (by
                      unfold nb067_alpha_dummy_181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                  (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                      unfold nb067_alpha_dummy_182;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                  ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                  ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                  ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
                  ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                  ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                  ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                  ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                  ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from (by
                    unfold nb067_alpha_dummy_181;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                    unfold nb067_alpha_dummy_182;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_181) from
                    (by
                      unfold nb067_alpha_dummy_181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                  (show (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_182 f) from (by
                      unfold nb067_alpha_dummy_182;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                  ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                  ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                  ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
                  ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                  ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                  ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                  ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                  ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part025`. -/


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

@[expose]
noncomputable def nb067_split_alpha_0053 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_199))
          (Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_199))
            (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_200 f))
          (Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_200 f))
            (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_170) from
                    (by
                      unfold nb067_alpha_dummy_170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))))
                  (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_172 f) from (by
                      unfold nb067_alpha_dummy_172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))))
                  (TAlphaVar.there (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_169) from
                      (by
                        unfold nb067_alpha_dummy_169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))))
                    (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_171 f) from (by
                        unfold nb067_alpha_dummy_171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0206 f) 0)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_199) from (by
                          unfold nb067_alpha_dummy_199;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0208) 0))))
                      (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_200 f) from (by
                          unfold nb067_alpha_dummy_200;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0209 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_173) from (by
                            unfold nb067_alpha_dummy_173;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0205) 0))))
                        (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_174 f) from (by
                            unfold nb067_alpha_dummy_174;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0207 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_163))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠
        (nb067_alpha_dummy_177) from (by
          unfold nb067_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_179 f) from (by
          unfold nb067_alpha_dummy_179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_178) from (by
          unfold nb067_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 1)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_180 f) from (by
          unfold nb067_alpha_dummy_180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_203) from (by
          unfold nb067_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0212) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_204 f) from (by
          unfold nb067_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0213 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_201) from (by
          unfold nb067_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0210) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_202 f) from (by
          unfold nb067_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0211 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0052 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠
        (nb067_alpha_dummy_177) from (by
          unfold nb067_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_179 f) from (by
          unfold nb067_alpha_dummy_179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_178) from (by
          unfold nb067_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 1)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_180 f) from (by
          unfold nb067_alpha_dummy_180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_203) from (by
          unfold nb067_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0212) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_204 f) from (by
          unfold nb067_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0213 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_201) from (by
          unfold nb067_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0210) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_202 f) from (by
          unfold nb067_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0211 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0052 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                          ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_170) from
                      (by
                        unfold nb067_alpha_dummy_170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))))
                    (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_172 f) from (by
                        unfold nb067_alpha_dummy_172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0206 f) 1)))) (TAlphaVar.there
                      (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_169) from (by
                          unfold nb067_alpha_dummy_169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0204) 0))))
                      (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_171 f) from (by
                          unfold nb067_alpha_dummy_171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0206 f) 0))))
                      (TAlphaVar.there
                        (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_199) from (by
                            unfold nb067_alpha_dummy_199;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0208) 0))))
                        (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_200 f) from (by
                            unfold nb067_alpha_dummy_200;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0209 f) 0))))
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_164) ≠ (nb067_alpha_dummy_173) from (by
                              unfold nb067_alpha_dummy_173;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0205) 0))))
                          (show (nb067_alpha_dummy_166 f) ≠ (nb067_alpha_dummy_174 f) from (by
                              unfold nb067_alpha_dummy_174;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0207 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_163))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_177) from (by
          unfold nb067_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_179 f) from (by
          unfold nb067_alpha_dummy_179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_178) from (by
          unfold nb067_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 1)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_180 f) from (by
          unfold nb067_alpha_dummy_180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_203) from (by
          unfold nb067_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0212) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_204 f) from (by
          unfold nb067_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0213 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_201)
        from (by
          unfold nb067_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0210)
                  0)))) (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_202 f) from (by
          unfold nb067_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0211 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0052 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_177) from (by
          unfold nb067_alpha_dummy_177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_179 f) from (by
          unfold nb067_alpha_dummy_179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_178) from (by
          unfold nb067_alpha_dummy_178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 1)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_180 f) from (by
          unfold nb067_alpha_dummy_180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_203) from (by
          unfold nb067_alpha_dummy_203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0212) 0)))) (show (nb067_alpha_dummy_172 f) ≠
        (nb067_alpha_dummy_204 f) from (by
          unfold nb067_alpha_dummy_204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0213 f)
                  0)))) (TAlphaVar.there (show (nb067_alpha_dummy_170) ≠ (nb067_alpha_dummy_201)
        from (by
          unfold nb067_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0210)
                  0)))) (show (nb067_alpha_dummy_172 f) ≠ (nb067_alpha_dummy_202 f) from (by
          unfold nb067_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0211 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067_split_alpha_0052 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                            ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                            ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                            ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                            ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                            ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                            ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                            ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                            ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                            ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                            ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                            ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0054 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
        ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
        ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
        ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
        ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_219))
            (syn_cun (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_222 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_223 f))
              (Class.cv (nb067_alpha_dummy_224 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
          ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
          ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
          ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
          ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
          ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
          ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
          ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
          ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
          ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_231) from (by
                                unfold nb067_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_232 f) from (by
                                unfold nb067_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_231) from (by
                                unfold nb067_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_232 f) from (by
                                unfold nb067_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_233) from (by
                                unfold nb067_alpha_dummy_233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_234 f) from (by
                                unfold nb067_alpha_dummy_234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_233) from (by
                                unfold nb067_alpha_dummy_233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_234 f) from (by
                                unfold nb067_alpha_dummy_234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0055 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_213))
          (Class.cv (nb067_alpha_dummy_206))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_214))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_213))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f))
          (Class.cv (nb067_alpha_dummy_208 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_216 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_215 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_213) from (by
              unfold nb067_alpha_dummy_213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 0))))
          (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_215 f) from (by
              unfold nb067_alpha_dummy_215;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb067_alpha_dummy_206) ≠ (nb067_alpha_dummy_214) from (by
                unfold nb067_alpha_dummy_214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 1))))
            (show (nb067_alpha_dummy_208 f) ≠ (nb067_alpha_dummy_216 f) from (by
                unfold nb067_alpha_dummy_216;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_206))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_208 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_220) from (by
                                  unfold nb067_alpha_dummy_220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0224) 1))))
                              (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_223 f) from
                                (by
                                  unfold nb067_alpha_dummy_223;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0225 f) 1))))
                              (TAlphaVar.there
                                (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_219) from (by
                                    unfold nb067_alpha_dummy_219;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0224) 0)))) (show
                                  (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_222 f) from (by
                                    unfold nb067_alpha_dummy_222;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from
                                    (by
                                      unfold nb067_alpha_dummy_217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0222)
                                              0)))) (show
                                    (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from
                                    (by
                                      unfold nb067_alpha_dummy_218;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
                                  ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
                                  ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
                                  ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                                  ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                                  ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                                  ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                                  ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                                  ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
                                  ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0054 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from (by
                          unfold nb067_alpha_dummy_217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                          unfold nb067_alpha_dummy_218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                      ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                      ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                      ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                      ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                      ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
                      ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                      ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                      ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                      ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from
                      (by
                        unfold nb067_alpha_dummy_217;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                    (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                        unfold nb067_alpha_dummy_218;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_217) from (by
                          unfold nb067_alpha_dummy_217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_218 f) from (by
                          unfold nb067_alpha_dummy_218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                      ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                      ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                      ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                      ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                      ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
                      ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                      ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                      ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                      ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0056 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
        ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
        ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
        ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
        ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
        ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_219))
            (syn_cun (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_222 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_223 f))
              (Class.cv (nb067_alpha_dummy_224 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_227) from (by
                              unfold nb067_alpha_dummy_227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_228 f) from (by
                              unfold nb067_alpha_dummy_228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_225) from (by
                                unfold nb067_alpha_dummy_225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_226 f) from (by
                                unfold nb067_alpha_dummy_226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
          ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
          ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
          ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
          ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
          ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
          ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
          ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
          ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
          ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
          ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
          ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_231) from (by
                                unfold nb067_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_232 f) from (by
                                unfold nb067_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_231) from (by
                                unfold nb067_alpha_dummy_231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_232 f) from (by
                                unfold nb067_alpha_dummy_232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_233) from (by
                                unfold nb067_alpha_dummy_233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_234 f) from (by
                                unfold nb067_alpha_dummy_234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_233) from (by
                                unfold nb067_alpha_dummy_233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_234 f) from (by
                                unfold nb067_alpha_dummy_234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067_alpha_dummy_221) ≠ (nb067_alpha_dummy_229) from (by
                                  unfold nb067_alpha_dummy_229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067_alpha_dummy_224 f) ≠ (nb067_alpha_dummy_230 f) from
                                (by
                                  unfold nb067_alpha_dummy_230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
