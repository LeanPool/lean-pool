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

/-- Checked nominal proof certificate identified upstream as `nb067_wpp_refl_0050`. -/
@[expose]
noncomputable def nb067WppRefl0050 (x : Var) (y : Var) (f : Var) :
    TReflOn
      [((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0050 x y f)

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0038`. -/
@[expose]
noncomputable def nb067SplitAlpha0038 (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Class.cab (nb067AlphaDummy081) (synWnan
          (Wff.classMem (Class.cv (nb067AlphaDummy081))
            (synCcom (Class.cv (nb067AlphaDummy000))
              (synCcnv (Class.cv (nb067AlphaDummy000)))))
          (Wff.classMem (Class.cv (nb067AlphaDummy081)) (synCid))))
      (Class.cab (nb067AlphaDummy082 f) (synWnan
          (Wff.classMem (Class.cv (nb067AlphaDummy082 f))
            (synCcom (Class.cv f) (synCcnv (Class.cv f))))
          (Wff.classMem (Class.cv (nb067AlphaDummy082 f)) (synCid)))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (Ne.symm
                          (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy089) from (by
                              unfold nb067AlphaDummy089;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0094) 0))))) (Ne.symm
                          (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy090 f) from (by
                              unfold nb067AlphaDummy090;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0095 f) 0)))))
                        (TAlphaVar.there (Ne.symm
                            (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy089) from (by
                                unfold nb067AlphaDummy089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0092) 0))))) (Ne.symm
                            (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy090 f) from (by
                                unfold nb067AlphaDummy090;
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
        (nb067AlphaDummy083) ≠ (nb067AlphaDummy092) from (by
          unfold nb067AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 1)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy094 f) from (by
          unfold nb067AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f)
                  1)))) (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy091)
        from (by
          unfold nb067AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096)
                  0)))) (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy093 f) from (by
          unfold nb067AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy097)
        from (by
          unfold nb067AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0100)
                  0)))) (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy098 f) from (by
          unfold nb067AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0101 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy095)
        from (by
          unfold nb067AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0097)
                  0)))) (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy096 f) from (by
          unfold nb067AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb067AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy083))).fv ∪
        ((Class.cv (nb067AlphaDummy084))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb067SplitAlpha0011 x y f))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb067AlphaDummy083) ≠ (nb067AlphaDummy092) from (by
          unfold nb067AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096) 1)))) (show (nb067AlphaDummy086 f) ≠
        (nb067AlphaDummy094 f) from (by
          unfold nb067AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f)
                  1)))) (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy091)
        from (by
          unfold nb067AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0096)
                  0)))) (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy093 f) from (by
          unfold nb067AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0098 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy097)
        from (by
          unfold nb067AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0100)
                  0)))) (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy098 f) from (by
          unfold nb067AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0101 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy083) ≠ (nb067AlphaDummy095)
        from (by
          unfold nb067AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0097)
                  0)))) (show (nb067AlphaDummy086 f) ≠ (nb067AlphaDummy096 f) from (by
          unfold nb067AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb067AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy083))).fv ∪
        ((Class.cv (nb067AlphaDummy084))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb067SplitAlpha0011 x y f)))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb067SplitAlpha0014 x y f)))))))))
                  (TAlphaWff.ex (TAlphaWff.neg (nb067SplitAlpha0037 x y f))))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfReflOn
            [((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
              ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
              ((nb067AlphaDummy000), f),
              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
            (synCid) (nb067WppRefl0050 x y f))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0039`. -/
@[expose]
noncomputable def nb067SplitAlpha0039 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
        ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
        ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
        ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
        ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
        ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
        ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
        ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
        ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy105))
            (synCun (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy108 f))
            (synCun (Class.cv (nb067AlphaDummy109 f))
              (Class.cv (nb067AlphaDummy110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy113) from (by
                              unfold nb067AlphaDummy113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0110) 0))))
                          (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy114 f) from (by
                              unfold nb067AlphaDummy114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0111 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy111) from (by
                                unfold nb067AlphaDummy111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0108) 0))))
                            (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy112 f) from (by
                                unfold nb067AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0109 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy113) from (by
                              unfold nb067AlphaDummy113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0114) 0))))
                          (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy114 f) from (by
                              unfold nb067AlphaDummy114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0115 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy111) from (by
                                unfold nb067AlphaDummy111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0112) 0))))
                            (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy112 f) from (by
                                unfold nb067AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0113 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy113) from (by
                              unfold nb067AlphaDummy113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0110) 0))))
                          (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy114 f) from (by
                              unfold nb067AlphaDummy114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0111 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy111) from (by
                                unfold nb067AlphaDummy111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0108) 0))))
                            (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy112 f) from (by
                                unfold nb067AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0109 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy113) from (by
                              unfold nb067AlphaDummy113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0114) 0))))
                          (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy114 f) from (by
                              unfold nb067AlphaDummy114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0115 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy111) from (by
                                unfold nb067AlphaDummy111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0112) 0))))
                            (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy112 f) from (by
                                unfold nb067AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0113 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
          ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
          ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
          ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
          ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
          ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
          ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
          ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
          ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
          ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy117) from (by
                                unfold nb067AlphaDummy117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0118) 0))))
                            (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy118 f) from (by
                                unfold nb067AlphaDummy118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0119 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy115) from (by
                                  unfold nb067AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0116) 0))))
                              (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy116 f) from
                                (by
                                  unfold nb067AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0117 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy117) from (by
                                unfold nb067AlphaDummy117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0118) 0))))
                            (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy118 f) from (by
                                unfold nb067AlphaDummy118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0119 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy115) from (by
                                  unfold nb067AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0116) 0))))
                              (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy116 f) from
                                (by
                                  unfold nb067AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0117 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy119) from (by
                                unfold nb067AlphaDummy119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0122) 0))))
                            (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy120 f) from (by
                                unfold nb067AlphaDummy120;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0123 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy115) from (by
                                  unfold nb067AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0120) 0))))
                              (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy116 f) from
                                (by
                                  unfold nb067AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0121 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy119) from (by
                                unfold nb067AlphaDummy119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0122) 0))))
                            (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy120 f) from (by
                                unfold nb067AlphaDummy120;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0123 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy115) from (by
                                  unfold nb067AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0120) 0))))
                              (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy116 f) from
                                (by
                                  unfold nb067AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0121 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0040`. -/
@[expose]
noncomputable def nb067SplitAlpha0040 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
        ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
        ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy091))
        (synCphi (Class.cv (nb067AlphaDummy092))))
      (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
        (synCphi (Class.cv (nb067AlphaDummy094 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb067AlphaDummy086 f))).fv ∪
            ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067AlphaDummy092) ≠ (nb067AlphaDummy099) from (by
                    unfold nb067AlphaDummy099;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 0))))
                (show (nb067AlphaDummy094 f) ≠ (nb067AlphaDummy101 f) from (by
                    unfold nb067AlphaDummy101;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 0))))
                (TAlphaVar.there (show (nb067AlphaDummy092) ≠ (nb067AlphaDummy100) from
                    (by
                      unfold nb067AlphaDummy100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 1))))
                  (show (nb067AlphaDummy094 f) ≠ (nb067AlphaDummy102 f) from (by
                      unfold nb067AlphaDummy102;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb067AlphaDummy092))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb067AlphaDummy094 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy106) from
                                    (by
                                      unfold nb067AlphaDummy106;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0106)
                                              1)))) (show
                                    (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy109 f) from
                                    (by
                                      unfold nb067AlphaDummy109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0107 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb067AlphaDummy099) ≠ (nb067AlphaDummy105) from (by
                                        unfold nb067AlphaDummy105;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0106)
                                                0)))) (show (nb067AlphaDummy101 f) ≠
                                        (nb067AlphaDummy108 f) from (by
                                        unfold nb067AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb067_support_mem_0107 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb067AlphaDummy099) ≠ (nb067AlphaDummy103) from
                                        (by
                                          unfold nb067AlphaDummy103;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb067_support_mem_0104)
                                                  0)))) (show (nb067AlphaDummy101 f) ≠
        (nb067AlphaDummy104 f) from (by
                                          unfold nb067AlphaDummy104;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb067_support_mem_0105 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
                                      ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
                                      ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
                                      ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                                      ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                                      ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                                      ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                                      ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                                      ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
                                      ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                      ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                        (nb067AlphaDummy004 x y f)),
                                      ((nb067AlphaDummy002), y),
                                      ((nb067AlphaDummy001), x), ((nb067AlphaDummy005),
                                        (nb067AlphaDummy006 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb067SplitAlpha0039 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy103) from (by
                              unfold nb067AlphaDummy103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                          (show (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy104 f) from (by
                              unfold nb067AlphaDummy104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                          ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                          ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                          ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                          ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                          ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
                          ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy103) from (by
                            unfold nb067AlphaDummy103;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                        (show (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy104 f) from (by
                            unfold nb067AlphaDummy104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy103) from (by
                              unfold nb067AlphaDummy103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                          (show (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy104 f) from (by
                              unfold nb067AlphaDummy104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                          ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                          ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                          ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                          ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                          ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
                          ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0041`. -/
@[expose]
noncomputable def nb067SplitAlpha0041 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
        ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
        ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
        ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
        ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
        ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
        ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
        ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
        ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
        ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
        ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy105))
            (synCun (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy108 f))
            (synCun (Class.cv (nb067AlphaDummy109 f))
              (Class.cv (nb067AlphaDummy110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy113) from (by
                              unfold nb067AlphaDummy113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0110) 0))))
                          (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy114 f) from (by
                              unfold nb067AlphaDummy114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0111 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy111) from (by
                                unfold nb067AlphaDummy111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0108) 0))))
                            (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy112 f) from (by
                                unfold nb067AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0109 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy113) from (by
                              unfold nb067AlphaDummy113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0114) 0))))
                          (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy114 f) from (by
                              unfold nb067AlphaDummy114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0115 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy111) from (by
                                unfold nb067AlphaDummy111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0112) 0))))
                            (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy112 f) from (by
                                unfold nb067AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0113 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy113) from (by
                              unfold nb067AlphaDummy113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0110) 0))))
                          (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy114 f) from (by
                              unfold nb067AlphaDummy114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0111 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy111) from (by
                                unfold nb067AlphaDummy111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0108) 0))))
                            (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy112 f) from (by
                                unfold nb067AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0109 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy113) from (by
                              unfold nb067AlphaDummy113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0114) 0))))
                          (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy114 f) from (by
                              unfold nb067AlphaDummy114;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0115 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy111) from (by
                                unfold nb067AlphaDummy111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0112) 0))))
                            (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy112 f) from (by
                                unfold nb067AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0113 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
          ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
          ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
          ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
          ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
          ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
          ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
          ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
          ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
          ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
          ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
          ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy117) from (by
                                unfold nb067AlphaDummy117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0118) 0))))
                            (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy118 f) from (by
                                unfold nb067AlphaDummy118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0119 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy115) from (by
                                  unfold nb067AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0116) 0))))
                              (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy116 f) from
                                (by
                                  unfold nb067AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0117 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy117) from (by
                                unfold nb067AlphaDummy117;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0118) 0))))
                            (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy118 f) from (by
                                unfold nb067AlphaDummy118;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0119 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy106) ≠ (nb067AlphaDummy115) from (by
                                  unfold nb067AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0116) 0))))
                              (show (nb067AlphaDummy109 f) ≠ (nb067AlphaDummy116 f) from
                                (by
                                  unfold nb067AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0117 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy119) from (by
                                unfold nb067AlphaDummy119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0122) 0))))
                            (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy120 f) from (by
                                unfold nb067AlphaDummy120;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0123 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy115) from (by
                                  unfold nb067AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0120) 0))))
                              (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy116 f) from
                                (by
                                  unfold nb067AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0121 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy119) from (by
                                unfold nb067AlphaDummy119;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0122) 0))))
                            (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy120 f) from (by
                                unfold nb067AlphaDummy120;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0123 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy107) ≠ (nb067AlphaDummy115) from (by
                                  unfold nb067AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0120) 0))))
                              (show (nb067AlphaDummy110 f) ≠ (nb067AlphaDummy116 f) from
                                (by
                                  unfold nb067AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0121 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0042`. -/
@[expose]
noncomputable def nb067SplitAlpha0042 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
        ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
        ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
        ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
        ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
        ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
        ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy099))
          (Class.cv (nb067AlphaDummy092))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy100))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy099)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy099)) (synC1c))
              (Class.cv (nb067AlphaDummy099))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy101 f))
          (Class.cv (nb067AlphaDummy094 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy102 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy101 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy101 f)) (synC1c))
              (Class.cv (nb067AlphaDummy101 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy092) ≠ (nb067AlphaDummy099) from (by
              unfold nb067AlphaDummy099;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 0))))
          (show (nb067AlphaDummy094 f) ≠ (nb067AlphaDummy101 f) from (by
              unfold nb067AlphaDummy101;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy092) ≠ (nb067AlphaDummy100) from (by
                unfold nb067AlphaDummy100;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 1))))
            (show (nb067AlphaDummy094 f) ≠ (nb067AlphaDummy102 f) from (by
                unfold nb067AlphaDummy102;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 1))))
            (TAlphaVar.there (show (nb067AlphaDummy092) ≠ (nb067AlphaDummy125) from (by
                  unfold nb067AlphaDummy125;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0132) 0))))
              (show (nb067AlphaDummy094 f) ≠ (nb067AlphaDummy126 f) from (by
                  unfold nb067AlphaDummy126;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0133 f) 0))))
              (TAlphaVar.there (show (nb067AlphaDummy092) ≠ (nb067AlphaDummy123) from (by
                    unfold nb067AlphaDummy123;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0130) 0))))
                (show (nb067AlphaDummy094 f) ≠ (nb067AlphaDummy124 f) from (by
                    unfold nb067AlphaDummy124;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0131 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy092))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy094 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy106) from (by
                                  unfold nb067AlphaDummy106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0106) 1))))
                              (show (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy109 f) from
                                (by
                                  unfold nb067AlphaDummy109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0107 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy105) from (by
                                    unfold nb067AlphaDummy105;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0106) 0)))) (show
                                  (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy108 f) from (by
                                    unfold nb067AlphaDummy108;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0107 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy103) from
                                    (by
                                      unfold nb067AlphaDummy103;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0104)
                                              0)))) (show
                                    (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy104 f) from
                                    (by
                                      unfold nb067AlphaDummy104;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0105 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
                                  ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
                                  ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
                                  ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                                  ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                                  ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                                  ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
                                  ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                                  ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                                  ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                                  ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                                  ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0041 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy103) from (by
                          unfold nb067AlphaDummy103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                      (show (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy104 f) from (by
                          unfold nb067AlphaDummy104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                      ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                      ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                      ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
                      ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                      ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                      ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                      ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                      ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy103) from
                      (by
                        unfold nb067AlphaDummy103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                    (show (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy104 f) from (by
                        unfold nb067AlphaDummy104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy099) ≠ (nb067AlphaDummy103) from (by
                          unfold nb067AlphaDummy103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0104) 0))))
                      (show (nb067AlphaDummy101 f) ≠ (nb067AlphaDummy104 f) from (by
                          unfold nb067AlphaDummy104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0105 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                      ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                      ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                      ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
                      ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                      ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                      ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                      ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                      ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0043`. -/
@[expose]
noncomputable def nb067SplitAlpha0043 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy121))
          (Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCun (synCphi (Class.cv (nb067AlphaDummy092))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy121))
            (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy122 f))
          (Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy122 f))
            (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy092) from
                    (by
                      unfold nb067AlphaDummy092;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))))
                  (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy094 f) from (by
                      unfold nb067AlphaDummy094;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy091) from
                      (by
                        unfold nb067AlphaDummy091;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))))
                    (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy093 f) from (by
                        unfold nb067AlphaDummy093;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0126 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy121) from (by
                          unfold nb067AlphaDummy121;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0128) 0))))
                      (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy122 f) from (by
                          unfold nb067AlphaDummy122;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0129 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy095) from (by
                            unfold nb067AlphaDummy095;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0125) 0))))
                        (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy096 f) from (by
                            unfold nb067AlphaDummy096;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0127 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy083))).fv ∪
                      ((Class.cv (nb067AlphaDummy084))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0042 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0042 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                          ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                          ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                          ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                          ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy092) from
                      (by
                        unfold nb067AlphaDummy092;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))))
                    (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy094 f) from (by
                        unfold nb067AlphaDummy094;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0126 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy091) from (by
                          unfold nb067AlphaDummy091;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0124) 0))))
                      (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy093 f) from (by
                          unfold nb067AlphaDummy093;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0126 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy121) from (by
                            unfold nb067AlphaDummy121;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0128) 0))))
                        (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy122 f) from (by
                            unfold nb067AlphaDummy122;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0129 f) 0))))
                        (TAlphaVar.there
                          (show (nb067AlphaDummy084) ≠ (nb067AlphaDummy095) from (by
                              unfold nb067AlphaDummy095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0125) 0))))
                          (show (nb067AlphaDummy087 f) ≠ (nb067AlphaDummy096 f) from (by
                              unfold nb067AlphaDummy096;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0127 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy083))).fv ∪
                        ((Class.cv (nb067AlphaDummy084))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0042 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0042 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                            ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                            ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                            ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                            ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                            ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                            ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                            ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0044`. -/
@[expose]
noncomputable def nb067SplitAlpha0044 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
        ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
        ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
        ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
        ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
        ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
        ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
        ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
        ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy141))
            (synCun (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy144 f))
            (synCun (Class.cv (nb067AlphaDummy145 f))
              (Class.cv (nb067AlphaDummy146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy149) from (by
                              unfold nb067AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0148) 0))))
                          (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy150 f) from (by
                              unfold nb067AlphaDummy150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0149 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy147) from (by
                                unfold nb067AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0146) 0))))
                            (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy148 f) from (by
                                unfold nb067AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0147 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy149) from (by
                              unfold nb067AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0152) 0))))
                          (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy150 f) from (by
                              unfold nb067AlphaDummy150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0153 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy147) from (by
                                unfold nb067AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0150) 0))))
                            (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy148 f) from (by
                                unfold nb067AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0151 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy149) from (by
                              unfold nb067AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0148) 0))))
                          (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy150 f) from (by
                              unfold nb067AlphaDummy150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0149 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy147) from (by
                                unfold nb067AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0146) 0))))
                            (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy148 f) from (by
                                unfold nb067AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0147 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy149) from (by
                              unfold nb067AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0152) 0))))
                          (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy150 f) from (by
                              unfold nb067AlphaDummy150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0153 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy147) from (by
                                unfold nb067AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0150) 0))))
                            (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy148 f) from (by
                                unfold nb067AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0151 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
          ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
          ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
          ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
          ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
          ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
          ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
          ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
          ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
          ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy153) from (by
                                unfold nb067AlphaDummy153;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0156) 0))))
                            (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy154 f) from (by
                                unfold nb067AlphaDummy154;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0157 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy151) from (by
                                  unfold nb067AlphaDummy151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0154) 0))))
                              (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy152 f) from
                                (by
                                  unfold nb067AlphaDummy152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0155 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy153) from (by
                                unfold nb067AlphaDummy153;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0156) 0))))
                            (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy154 f) from (by
                                unfold nb067AlphaDummy154;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0157 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy151) from (by
                                  unfold nb067AlphaDummy151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0154) 0))))
                              (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy152 f) from
                                (by
                                  unfold nb067AlphaDummy152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0155 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy155) from (by
                                unfold nb067AlphaDummy155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0160) 0))))
                            (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy156 f) from (by
                                unfold nb067AlphaDummy156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0161 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy151) from (by
                                  unfold nb067AlphaDummy151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0158) 0))))
                              (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy152 f) from
                                (by
                                  unfold nb067AlphaDummy152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0159 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy155) from (by
                                unfold nb067AlphaDummy155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0160) 0))))
                            (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy156 f) from (by
                                unfold nb067AlphaDummy156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0161 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy151) from (by
                                  unfold nb067AlphaDummy151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0158) 0))))
                              (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy152 f) from
                                (by
                                  unfold nb067AlphaDummy152;
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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0045`. -/
@[expose]
noncomputable def nb067SplitAlpha0045 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
        ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
        ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
        ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
        ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy135))
            (Class.cv (nb067AlphaDummy128))) (Wff.classEq (Class.cv (nb067AlphaDummy136))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy135)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy135)) (synC1c))
              (Class.cv (nb067AlphaDummy135))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy137 f))
            (Class.cv (nb067AlphaDummy130 f)))
          (Wff.classEq (Class.cv (nb067AlphaDummy138 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy137 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy137 f)) (synC1c))
              (Class.cv (nb067AlphaDummy137 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb067AlphaDummy128) ≠ (nb067AlphaDummy135) from (by
                unfold nb067AlphaDummy135;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 0))))
            (show (nb067AlphaDummy130 f) ≠ (nb067AlphaDummy137 f) from (by
                unfold nb067AlphaDummy137;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 0))))
            (TAlphaVar.there (show (nb067AlphaDummy128) ≠ (nb067AlphaDummy136) from (by
                  unfold nb067AlphaDummy136;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 1))))
              (show (nb067AlphaDummy130 f) ≠ (nb067AlphaDummy138 f) from (by
                  unfold nb067AlphaDummy138;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy128))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy130 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy142) from (by
                                  unfold nb067AlphaDummy142;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0144) 1))))
                              (show (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy145 f) from
                                (by
                                  unfold nb067AlphaDummy145;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0145 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy141) from (by
                                    unfold nb067AlphaDummy141;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0144) 0)))) (show
                                  (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy144 f) from (by
                                    unfold nb067AlphaDummy144;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0145 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy139) from
                                    (by
                                      unfold nb067AlphaDummy139;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0142)
                                              0)))) (show
                                    (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy140 f) from
                                    (by
                                      unfold nb067AlphaDummy140;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0143 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
                                  ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
                                  ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
                                  ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                                  ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                                  ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                                  ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                                  ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                                  ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
                                  ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0044 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy139) from (by
                          unfold nb067AlphaDummy139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                      (show (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy140 f) from (by
                          unfold nb067AlphaDummy140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                      ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                      ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                      ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                      ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                      ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
                      ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy139) from
                      (by
                        unfold nb067AlphaDummy139;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                    (show (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy140 f) from (by
                        unfold nb067AlphaDummy140;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy139) from (by
                          unfold nb067AlphaDummy139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                      (show (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy140 f) from (by
                          unfold nb067AlphaDummy140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                      ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                      ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                      ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                      ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                      ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
                      ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0046`. -/
@[expose]
noncomputable def nb067SplitAlpha0046 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
        ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
        ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
        ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
        ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
        ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
        ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
        ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
        ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
        ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
        ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy141))
            (synCun (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy144 f))
            (synCun (Class.cv (nb067AlphaDummy145 f))
              (Class.cv (nb067AlphaDummy146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy149) from (by
                              unfold nb067AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0148) 0))))
                          (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy150 f) from (by
                              unfold nb067AlphaDummy150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0149 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy147) from (by
                                unfold nb067AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0146) 0))))
                            (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy148 f) from (by
                                unfold nb067AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0147 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy149) from (by
                              unfold nb067AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0152) 0))))
                          (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy150 f) from (by
                              unfold nb067AlphaDummy150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0153 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy147) from (by
                                unfold nb067AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0150) 0))))
                            (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy148 f) from (by
                                unfold nb067AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0151 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy149) from (by
                              unfold nb067AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0148) 0))))
                          (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy150 f) from (by
                              unfold nb067AlphaDummy150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0149 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy147) from (by
                                unfold nb067AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0146) 0))))
                            (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy148 f) from (by
                                unfold nb067AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0147 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy149) from (by
                              unfold nb067AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0152) 0))))
                          (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy150 f) from (by
                              unfold nb067AlphaDummy150;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0153 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy147) from (by
                                unfold nb067AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0150) 0))))
                            (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy148 f) from (by
                                unfold nb067AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0151 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
          ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
          ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
          ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
          ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
          ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
          ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
          ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
          ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
          ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
          ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
          ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy153) from (by
                                unfold nb067AlphaDummy153;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0156) 0))))
                            (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy154 f) from (by
                                unfold nb067AlphaDummy154;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0157 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy151) from (by
                                  unfold nb067AlphaDummy151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0154) 0))))
                              (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy152 f) from
                                (by
                                  unfold nb067AlphaDummy152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0155 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy153) from (by
                                unfold nb067AlphaDummy153;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0156) 0))))
                            (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy154 f) from (by
                                unfold nb067AlphaDummy154;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0157 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy142) ≠ (nb067AlphaDummy151) from (by
                                  unfold nb067AlphaDummy151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0154) 0))))
                              (show (nb067AlphaDummy145 f) ≠ (nb067AlphaDummy152 f) from
                                (by
                                  unfold nb067AlphaDummy152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0155 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy155) from (by
                                unfold nb067AlphaDummy155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0160) 0))))
                            (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy156 f) from (by
                                unfold nb067AlphaDummy156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0161 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy151) from (by
                                  unfold nb067AlphaDummy151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0158) 0))))
                              (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy152 f) from
                                (by
                                  unfold nb067AlphaDummy152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0159 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy155) from (by
                                unfold nb067AlphaDummy155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0160) 0))))
                            (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy156 f) from (by
                                unfold nb067AlphaDummy156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0161 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy143) ≠ (nb067AlphaDummy151) from (by
                                  unfold nb067AlphaDummy151;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0158) 0))))
                              (show (nb067AlphaDummy146 f) ≠ (nb067AlphaDummy152 f) from
                                (by
                                  unfold nb067AlphaDummy152;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0159 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0047`. -/
@[expose]
noncomputable def nb067SplitAlpha0047 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
        ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
        ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
        ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
        ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
        ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
        ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy135))
          (Class.cv (nb067AlphaDummy128))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy136))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy135)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy135)) (synC1c))
              (Class.cv (nb067AlphaDummy135))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy137 f))
          (Class.cv (nb067AlphaDummy130 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy138 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy137 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy137 f)) (synC1c))
              (Class.cv (nb067AlphaDummy137 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy128) ≠ (nb067AlphaDummy135) from (by
              unfold nb067AlphaDummy135;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 0))))
          (show (nb067AlphaDummy130 f) ≠ (nb067AlphaDummy137 f) from (by
              unfold nb067AlphaDummy137;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy128) ≠ (nb067AlphaDummy136) from (by
                unfold nb067AlphaDummy136;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 1))))
            (show (nb067AlphaDummy130 f) ≠ (nb067AlphaDummy138 f) from (by
                unfold nb067AlphaDummy138;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 1))))
            (TAlphaVar.there (show (nb067AlphaDummy128) ≠ (nb067AlphaDummy161) from (by
                  unfold nb067AlphaDummy161;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0170) 0))))
              (show (nb067AlphaDummy130 f) ≠ (nb067AlphaDummy162 f) from (by
                  unfold nb067AlphaDummy162;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0171 f) 0))))
              (TAlphaVar.there (show (nb067AlphaDummy128) ≠ (nb067AlphaDummy159) from (by
                    unfold nb067AlphaDummy159;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0168) 0))))
                (show (nb067AlphaDummy130 f) ≠ (nb067AlphaDummy160 f) from (by
                    unfold nb067AlphaDummy160;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0169 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy128))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy130 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy142) from (by
                                  unfold nb067AlphaDummy142;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0144) 1))))
                              (show (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy145 f) from
                                (by
                                  unfold nb067AlphaDummy145;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0145 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy141) from (by
                                    unfold nb067AlphaDummy141;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0144) 0)))) (show
                                  (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy144 f) from (by
                                    unfold nb067AlphaDummy144;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0145 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy139) from
                                    (by
                                      unfold nb067AlphaDummy139;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0142)
                                              0)))) (show
                                    (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy140 f) from
                                    (by
                                      unfold nb067AlphaDummy140;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0143 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
                                  ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
                                  ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
                                  ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                                  ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                                  ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                                  ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
                                  ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                                  ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                                  ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                                  ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                                  ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0046 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy139) from (by
                          unfold nb067AlphaDummy139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                      (show (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy140 f) from (by
                          unfold nb067AlphaDummy140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                      ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                      ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                      ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
                      ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                      ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                      ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                      ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                      ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy139) from
                      (by
                        unfold nb067AlphaDummy139;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                    (show (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy140 f) from (by
                        unfold nb067AlphaDummy140;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy135) ≠ (nb067AlphaDummy139) from (by
                          unfold nb067AlphaDummy139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0142) 0))))
                      (show (nb067AlphaDummy137 f) ≠ (nb067AlphaDummy140 f) from (by
                          unfold nb067AlphaDummy140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0143 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                      ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                      ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                      ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
                      ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                      ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                      ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                      ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                      ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0048`. -/
@[expose]
noncomputable def nb067SplitAlpha0048 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy157))
          (Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCun (synCphi (Class.cv (nb067AlphaDummy128))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy157))
            (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy158 f))
          (Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy158 f))
            (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy085) ≠ (nb067AlphaDummy128) from
                    (by
                      unfold nb067AlphaDummy128;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))))
                  (show (nb067AlphaDummy088 f) ≠ (nb067AlphaDummy130 f) from (by
                      unfold nb067AlphaDummy130;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy085) ≠ (nb067AlphaDummy127) from
                      (by
                        unfold nb067AlphaDummy127;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))))
                    (show (nb067AlphaDummy088 f) ≠ (nb067AlphaDummy129 f) from (by
                        unfold nb067AlphaDummy129;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0164 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy085) ≠ (nb067AlphaDummy157) from (by
                          unfold nb067AlphaDummy157;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0166) 0))))
                      (show (nb067AlphaDummy088 f) ≠ (nb067AlphaDummy158 f) from (by
                          unfold nb067AlphaDummy158;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0167 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy085) ≠ (nb067AlphaDummy131) from (by
                            unfold nb067AlphaDummy131;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0163) 0))))
                        (show (nb067AlphaDummy088 f) ≠ (nb067AlphaDummy132 f) from (by
                            unfold nb067AlphaDummy132;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0165 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy083))).fv ∪
                      ((Class.cv (nb067AlphaDummy085))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy088 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0047 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0047 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                          ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                          ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                          ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                          ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy085) ≠ (nb067AlphaDummy128) from
                      (by
                        unfold nb067AlphaDummy128;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))))
                    (show (nb067AlphaDummy088 f) ≠ (nb067AlphaDummy130 f) from (by
                        unfold nb067AlphaDummy130;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0164 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy085) ≠ (nb067AlphaDummy127) from (by
                          unfold nb067AlphaDummy127;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0162) 0))))
                      (show (nb067AlphaDummy088 f) ≠ (nb067AlphaDummy129 f) from (by
                          unfold nb067AlphaDummy129;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0164 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy085) ≠ (nb067AlphaDummy157) from (by
                            unfold nb067AlphaDummy157;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0166) 0))))
                        (show (nb067AlphaDummy088 f) ≠ (nb067AlphaDummy158 f) from (by
                            unfold nb067AlphaDummy158;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0167 f) 0))))
                        (TAlphaVar.there
                          (show (nb067AlphaDummy085) ≠ (nb067AlphaDummy131) from (by
                              unfold nb067AlphaDummy131;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0163) 0))))
                          (show (nb067AlphaDummy088 f) ≠ (nb067AlphaDummy132 f) from (by
                              unfold nb067AlphaDummy132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0165 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy083))).fv ∪
                        ((Class.cv (nb067AlphaDummy085))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy088 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0047 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0047 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                            ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                            ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                            ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                            ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                            ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                            ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                            ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                            ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0049`. -/
@[expose]
noncomputable def nb067SplitAlpha0049 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
        ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
        ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
        ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
        ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy183))
            (synCun (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy186 f))
            (synCun (Class.cv (nb067AlphaDummy187 f))
              (Class.cv (nb067AlphaDummy188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
          ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
          ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
          ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
          ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
          ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
          ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy195) from (by
                                unfold nb067AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy196 f) from (by
                                unfold nb067AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy195) from (by
                                unfold nb067AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy196 f) from (by
                                unfold nb067AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy197) from (by
                                unfold nb067AlphaDummy197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy198 f) from (by
                                unfold nb067AlphaDummy198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy197) from (by
                                unfold nb067AlphaDummy197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy198 f) from (by
                                unfold nb067AlphaDummy198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0050`. -/
@[expose]
noncomputable def nb067SplitAlpha0050 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy177))
          (Class.cv (nb067AlphaDummy170))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy178))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy177)) (synC1c))
              (Class.cv (nb067AlphaDummy177))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy179 f))
          (Class.cv (nb067AlphaDummy172 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy180 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c))
              (Class.cv (nb067AlphaDummy179 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy177) from (by
              unfold nb067AlphaDummy177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0))))
          (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy179 f) from (by
              unfold nb067AlphaDummy179;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy178) from (by
                unfold nb067AlphaDummy178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1))))
            (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy180 f) from (by
                unfold nb067AlphaDummy180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy170))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy172 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy184) from (by
                                  unfold nb067AlphaDummy184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0186) 1))))
                              (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy187 f) from
                                (by
                                  unfold nb067AlphaDummy187;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0187 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy183) from (by
                                    unfold nb067AlphaDummy183;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0186) 0)))) (show
                                  (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy186 f) from (by
                                    unfold nb067AlphaDummy186;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0187 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from
                                    (by
                                      unfold nb067AlphaDummy181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0184)
                                              0)))) (show
                                    (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from
                                    (by
                                      unfold nb067AlphaDummy182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0185 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
                                  ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
                                  ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
                                  ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                                  ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                                  ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                                  ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                                  ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                                  ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
                                  ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0049 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from (by
                          unfold nb067AlphaDummy181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                          unfold nb067AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                      ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                      ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                      ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                      ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                      ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
                      ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                      ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                      ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                      ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from
                      (by
                        unfold nb067AlphaDummy181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                    (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                        unfold nb067AlphaDummy182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from (by
                          unfold nb067AlphaDummy181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                      (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                          unfold nb067AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                      ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                      ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                      ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                      ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                      ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
                      ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                      ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                      ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                      ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0051`. -/
@[expose]
noncomputable def nb067SplitAlpha0051 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
        ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
        ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
        ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
        ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
        ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy183))
            (synCun (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy186 f))
            (synCun (Class.cv (nb067AlphaDummy187 f))
              (Class.cv (nb067AlphaDummy188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0190) 0))))
                          (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0191 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0188) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0189 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy191) from (by
                              unfold nb067AlphaDummy191;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0194) 0))))
                          (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy192 f) from (by
                              unfold nb067AlphaDummy192;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy189) from (by
                                unfold nb067AlphaDummy189;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0192) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy190 f) from (by
                                unfold nb067AlphaDummy190;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0193 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
          ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
          ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
          ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
          ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
          ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
          ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
          ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
          ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy195) from (by
                                unfold nb067AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy196 f) from (by
                                unfold nb067AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy195) from (by
                                unfold nb067AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0198) 0))))
                            (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy196 f) from (by
                                unfold nb067AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0199 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy184) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0196) 0))))
                              (show (nb067AlphaDummy187 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0197 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy197) from (by
                                unfold nb067AlphaDummy197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy198 f) from (by
                                unfold nb067AlphaDummy198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy197) from (by
                                unfold nb067AlphaDummy197;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0202) 0))))
                            (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy198 f) from (by
                                unfold nb067AlphaDummy198;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0203 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy185) ≠ (nb067AlphaDummy193) from (by
                                  unfold nb067AlphaDummy193;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0200) 0))))
                              (show (nb067AlphaDummy188 f) ≠ (nb067AlphaDummy194 f) from
                                (by
                                  unfold nb067AlphaDummy194;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0201 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0052`. -/
@[expose]
noncomputable def nb067SplitAlpha0052 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
        ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy178))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy177)) (synC1c))
          (Class.cv (nb067AlphaDummy177))))
      (Wff.classEq (Class.cv (nb067AlphaDummy180 f))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c))
          (Class.cv (nb067AlphaDummy179 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067AlphaDummy170))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067AlphaDummy172 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy184) from (by
                              unfold nb067AlphaDummy184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0186) 1))))
                          (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy187 f) from (by
                              unfold nb067AlphaDummy187;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0187 f) 1))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy183) from (by
                                unfold nb067AlphaDummy183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0186) 0))))
                            (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy186 f) from (by
                                unfold nb067AlphaDummy186;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from (by
                                  unfold nb067AlphaDummy181;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                              (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from
                                (by
                                  unfold nb067AlphaDummy182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
                              ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
                              ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
                              ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                              ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                              ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                              ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
                              ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                              ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                              ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                              ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                              ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                              ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                              ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                              ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                              ((nb067AlphaDummy000), f),
                              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067SplitAlpha0051 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from (by
                      unfold nb067AlphaDummy181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                  (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                      unfold nb067AlphaDummy182;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                  ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                  ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                  ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
                  ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                  ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                  ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                  ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                  ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from (by
                    unfold nb067AlphaDummy181;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                    unfold nb067AlphaDummy182;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy177) ≠ (nb067AlphaDummy181) from
                    (by
                      unfold nb067AlphaDummy181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))))
                  (show (nb067AlphaDummy179 f) ≠ (nb067AlphaDummy182 f) from (by
                      unfold nb067AlphaDummy182;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                  ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                  ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                  ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
                  ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                  ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                  ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                  ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                  ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0053`. -/
@[expose]
noncomputable def nb067SplitAlpha0053 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy199))
          (Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy199))
            (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy200 f))
          (Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy200 f))
            (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy170) from
                    (by
                      unfold nb067AlphaDummy170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))))
                  (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy172 f) from (by
                      unfold nb067AlphaDummy172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))))
                  (TAlphaVar.there (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy169) from
                      (by
                        unfold nb067AlphaDummy169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))))
                    (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy171 f) from (by
                        unfold nb067AlphaDummy171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0206 f) 0)))) (TAlphaVar.there
                      (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy199) from (by
                          unfold nb067AlphaDummy199;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0208) 0))))
                      (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy200 f) from (by
                          unfold nb067AlphaDummy200;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0209 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy173) from (by
                            unfold nb067AlphaDummy173;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0205) 0))))
                        (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy174 f) from (by
                            unfold nb067AlphaDummy174;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0207 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy163))).fv ∪
                      ((Class.cv (nb067AlphaDummy164))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy165 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067AlphaDummy170) ≠
        (nb067AlphaDummy177) from (by
          unfold nb067AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy179 f) from (by
          unfold nb067AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy178) from (by
          unfold nb067AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 1)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy180 f) from (by
          unfold nb067AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy203) from (by
          unfold nb067AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0212) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy204 f) from (by
          unfold nb067AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0213 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy201) from (by
          unfold nb067AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0210) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy202 f) from (by
          unfold nb067AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0211 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0052 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb067AlphaDummy170) ≠
        (nb067AlphaDummy177) from (by
          unfold nb067AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy179 f) from (by
          unfold nb067AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy178) from (by
          unfold nb067AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 1)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy180 f) from (by
          unfold nb067AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy203) from (by
          unfold nb067AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0212) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy204 f) from (by
          unfold nb067AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0213 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy201) from (by
          unfold nb067AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0210) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy202 f) from (by
          unfold nb067AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0211 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0052 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                          ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy170) from
                      (by
                        unfold nb067AlphaDummy170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))))
                    (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy172 f) from (by
                        unfold nb067AlphaDummy172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0206 f) 1)))) (TAlphaVar.there
                      (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy169) from (by
                          unfold nb067AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0204) 0))))
                      (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy171 f) from (by
                          unfold nb067AlphaDummy171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0206 f) 0))))
                      (TAlphaVar.there
                        (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy199) from (by
                            unfold nb067AlphaDummy199;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0208) 0))))
                        (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy200 f) from (by
                            unfold nb067AlphaDummy200;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0209 f) 0))))
                        (TAlphaVar.there
                          (show (nb067AlphaDummy164) ≠ (nb067AlphaDummy173) from (by
                              unfold nb067AlphaDummy173;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0205) 0))))
                          (show (nb067AlphaDummy166 f) ≠ (nb067AlphaDummy174 f) from (by
                              unfold nb067AlphaDummy174;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0207 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy163))).fv ∪
                        ((Class.cv (nb067AlphaDummy164))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy165 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy177) from (by
          unfold nb067AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy179 f) from (by
          unfold nb067AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy178) from (by
          unfold nb067AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 1)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy180 f) from (by
          unfold nb067AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy203) from (by
          unfold nb067AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0212) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy204 f) from (by
          unfold nb067AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0213 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy201)
        from (by
          unfold nb067AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0210)
                  0)))) (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy202 f) from (by
          unfold nb067AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0211 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0052 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy177) from (by
          unfold nb067AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy179 f) from (by
          unfold nb067AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy178) from (by
          unfold nb067AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0182) 1)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy180 f) from (by
          unfold nb067AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb067AlphaDummy170) ≠ (nb067AlphaDummy203) from (by
          unfold nb067AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0212) 0)))) (show (nb067AlphaDummy172 f) ≠
        (nb067AlphaDummy204 f) from (by
          unfold nb067AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0213 f)
                  0)))) (TAlphaVar.there (show (nb067AlphaDummy170) ≠ (nb067AlphaDummy201)
        from (by
          unfold nb067AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0210)
                  0)))) (show (nb067AlphaDummy172 f) ≠ (nb067AlphaDummy202 f) from (by
          unfold nb067AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb067_support_mem_0211 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb067SplitAlpha0052 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                            ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                            ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                            ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                            ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                            ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                            ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                            ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                            ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                            ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                            ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                            ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0054`. -/
@[expose]
noncomputable def nb067SplitAlpha0054 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
        ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
        ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
        ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
        ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
        ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
        ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy219))
            (synCun (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy222 f))
            (synCun (Class.cv (nb067AlphaDummy223 f))
              (Class.cv (nb067AlphaDummy224 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
          ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
          ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
          ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
          ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
          ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
          ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
          ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
          ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
          ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy231) from (by
                                unfold nb067AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy232 f) from (by
                                unfold nb067AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy231) from (by
                                unfold nb067AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy232 f) from (by
                                unfold nb067AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy233) from (by
                                unfold nb067AlphaDummy233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy234 f) from (by
                                unfold nb067AlphaDummy234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy233) from (by
                                unfold nb067AlphaDummy233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy234 f) from (by
                                unfold nb067AlphaDummy234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0055`. -/
@[expose]
noncomputable def nb067SplitAlpha0055 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
        ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
        ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy213))
          (Class.cv (nb067AlphaDummy206))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy214))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy213)) (synC1c))
              (Class.cv (nb067AlphaDummy213))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy215 f))
          (Class.cv (nb067AlphaDummy208 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy216 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c))
              (Class.cv (nb067AlphaDummy215 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy213) from (by
              unfold nb067AlphaDummy213;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 0))))
          (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy215 f) from (by
              unfold nb067AlphaDummy215;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 0))))
          (TAlphaVar.there (show (nb067AlphaDummy206) ≠ (nb067AlphaDummy214) from (by
                unfold nb067AlphaDummy214;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0220) 1))))
            (show (nb067AlphaDummy208 f) ≠ (nb067AlphaDummy216 f) from (by
                unfold nb067AlphaDummy216;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0221 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy206))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy208 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy220) from (by
                                  unfold nb067AlphaDummy220;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0224) 1))))
                              (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy223 f) from
                                (by
                                  unfold nb067AlphaDummy223;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0225 f) 1))))
                              (TAlphaVar.there
                                (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy219) from (by
                                    unfold nb067AlphaDummy219;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0224) 0)))) (show
                                  (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy222 f) from (by
                                    unfold nb067AlphaDummy222;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb067_support_mem_0225 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from
                                    (by
                                      unfold nb067AlphaDummy217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0222)
                                              0)))) (show
                                    (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from
                                    (by
                                      unfold nb067AlphaDummy218;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb067_support_mem_0223 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
                                  ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
                                  ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
                                  ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                                  ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                                  ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                                  ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                                  ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                                  ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
                                  ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0054 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from (by
                          unfold nb067AlphaDummy217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                          unfold nb067AlphaDummy218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                      ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                      ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                      ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                      ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                      ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
                      ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                      ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                      ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                      ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from
                      (by
                        unfold nb067AlphaDummy217;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                    (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                        unfold nb067AlphaDummy218;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb067AlphaDummy213) ≠ (nb067AlphaDummy217) from (by
                          unfold nb067AlphaDummy217;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0222) 0))))
                      (show (nb067AlphaDummy215 f) ≠ (nb067AlphaDummy218 f) from (by
                          unfold nb067AlphaDummy218;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb067_support_mem_0223 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                      ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                      ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                      ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                      ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                      ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
                      ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                      ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                      ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                      ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0056`. -/
@[expose]
noncomputable def nb067SplitAlpha0056 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
        ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
        ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
        ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
        ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
        ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
        ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
        ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
        ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy219))
            (synCun (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy222 f))
            (synCun (Class.cv (nb067AlphaDummy223 f))
              (Class.cv (nb067AlphaDummy224 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0228) 0))))
                          (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0229 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0226) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0227 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy227) from (by
                              unfold nb067AlphaDummy227;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0232) 0))))
                          (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy228 f) from (by
                              unfold nb067AlphaDummy228;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0233 f) 0))))
                          (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy225) from (by
                                unfold nb067AlphaDummy225;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0230) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy226 f) from (by
                                unfold nb067AlphaDummy226;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0231 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
          ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
          ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
          ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
          ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
          ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
          ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
          ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
          ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
          ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
          ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
          ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy231) from (by
                                unfold nb067AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy232 f) from (by
                                unfold nb067AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy231) from (by
                                unfold nb067AlphaDummy231;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0236) 0))))
                            (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy232 f) from (by
                                unfold nb067AlphaDummy232;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0237 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy220) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0234) 0))))
                              (show (nb067AlphaDummy223 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0235 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy233) from (by
                                unfold nb067AlphaDummy233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy234 f) from (by
                                unfold nb067AlphaDummy234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy233) from (by
                                unfold nb067AlphaDummy233;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0240) 0))))
                            (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy234 f) from (by
                                unfold nb067AlphaDummy234;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0241 f) 0))))
                            (TAlphaVar.there
                              (show (nb067AlphaDummy221) ≠ (nb067AlphaDummy229) from (by
                                  unfold nb067AlphaDummy229;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0238) 0))))
                              (show (nb067AlphaDummy224 f) ≠ (nb067AlphaDummy230 f) from
                                (by
                                  unfold nb067AlphaDummy230;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0239 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
