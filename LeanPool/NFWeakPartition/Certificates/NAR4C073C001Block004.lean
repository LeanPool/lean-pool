/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C073C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C073C001Part008`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb073_split_alpha_0004`. -/
@[expose]
noncomputable def nb073SplitAlpha0004 (x : Var) (y : Var) :
    TAlphaWff
      [((nb073AlphaDummy086), (nb073AlphaDummy087 x y)),
        ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
        ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
        ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
        ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy086))
          (Class.cab (nb073AlphaDummy080)
            (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
              (Wff.classEq (Class.cv (nb073AlphaDummy080))
                (synCphi (Class.cv (nb073AlphaDummy081))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy086)) (Class.cab (nb073AlphaDummy080)
              (synWrex (nb073AlphaDummy081) (Class.cv (nb073AlphaDummy014))
                (Wff.classEq (Class.cv (nb073AlphaDummy080))
                  (synCphi (Class.cv (nb073AlphaDummy081)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy087 x y))
          (Class.cab (nb073AlphaDummy082 x y)
            (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
              (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                (synCphi (Class.cv (nb073AlphaDummy083 x y))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy087 x y))
            (Class.cab (nb073AlphaDummy082 x y)
              (synWrex (nb073AlphaDummy083 x y) (Class.cv (nb073AlphaDummy016 x y))
                (Wff.classEq (Class.cv (nb073AlphaDummy082 x y))
                  (synCphi (Class.cv (nb073AlphaDummy083 x y))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy081) from
                    (by
                      unfold nb073AlphaDummy081;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))))
                  (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy083 x y) from (by
                      unfold nb073AlphaDummy083;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb073_support_mem_0098 x y) 1)))) (TAlphaVar.there
                    (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy080) from (by
                        unfold nb073AlphaDummy080;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 0))))
                    (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy082 x y) from (by
                        unfold nb073AlphaDummy082;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))))
                    (TAlphaVar.there
                      (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy086) from (by
                          unfold nb073AlphaDummy086;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0100) 0))))
                      (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy087 x y) from (by
                          unfold nb073AlphaDummy087;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0101 x y) 0))))
                      (TAlphaVar.there
                        (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy084) from (by
                            unfold nb073AlphaDummy084;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0097) 0))))
                        (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy085 x y) from (by
                            unfold nb073AlphaDummy085;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0099 x y) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb073AlphaDummy000))).fv ∪
                              ((Class.cv (nb073AlphaDummy001))).fv) (by decide))
                          (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb073AlphaDummy014))).fv ∪
                      ((Class.cv (nb073AlphaDummy015))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
                      ((Class.cv (nb073AlphaDummy017 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy088) from (by
                              unfold nb073AlphaDummy088;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0102) 0))))
                          (show (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy090 x y) from
                            (by
                              unfold nb073AlphaDummy090;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0103 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy089) from (by
                                unfold nb073AlphaDummy089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0102) 1)))) (show
                              (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy091 x y) from (by
                                unfold nb073AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0103 x y) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073AlphaDummy081))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073AlphaDummy083 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy095) from (by
          unfold nb073AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 1)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy098 x y) from (by
          unfold nb073AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy088) ≠ (nb073AlphaDummy094) from (by
          unfold nb073AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 0)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy097 x y) from (by
          unfold nb073AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy092)
        from (by
          unfold nb073AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0104) 0)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy093 x y) from (by
          unfold nb073AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0105 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy096), (nb073AlphaDummy099 x y)), ((nb073AlphaDummy095),
        (nb073AlphaDummy098 x y)), ((nb073AlphaDummy094), (nb073AlphaDummy097 x y)),
        ((nb073AlphaDummy092), (nb073AlphaDummy093 x y)), ((nb073AlphaDummy088),
        (nb073AlphaDummy090 x y)), ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
        ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)), ((nb073AlphaDummy080),
        (nb073AlphaDummy082 x y)), ((nb073AlphaDummy086), (nb073AlphaDummy087 x y)),
        ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)), ((nb073AlphaDummy015),
        (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
        ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy102) from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy102)
        from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy102) from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy102)
        from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy096), (nb073AlphaDummy099 x y)), ((nb073AlphaDummy095),
        (nb073AlphaDummy098 x y)), ((nb073AlphaDummy094), (nb073AlphaDummy097 x y)),
        ((nb073AlphaDummy092), (nb073AlphaDummy093 x y)), ((nb073AlphaDummy088),
        (nb073AlphaDummy090 x y)), ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
        ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)), ((nb073AlphaDummy080),
        (nb073AlphaDummy082 x y)), ((nb073AlphaDummy086), (nb073AlphaDummy087 x y)),
        ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)), ((nb073AlphaDummy015),
        (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
        ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy088))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy090 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy095) ≠
        (nb073AlphaDummy106) from (by
          unfold
            nb073AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy107 x y) from (by
          unfold
            nb073AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy106)
        from (by
          unfold
            nb073AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy107 x y) from (by
          unfold
            nb073AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy108) from (by
          unfold
            nb073AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy109 x y) from (by
          unfold
            nb073AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠
        (nb073AlphaDummy108) from (by
          unfold
            nb073AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy109 x y) from (by
          unfold
            nb073AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from (by
                                        unfold nb073AlphaDummy092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073AlphaDummy090 x y) ≠
                                        (nb073AlphaDummy093 x y) from (by
                                        unfold nb073AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy092), (nb073AlphaDummy093 x y)),
                                    ((nb073AlphaDummy088), (nb073AlphaDummy090 x y)),
                                    ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
                                    ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
                                    ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
                                    ((nb073AlphaDummy086), (nb073AlphaDummy087 x y)),
                                    ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from
                                    (by
                                      unfold nb073AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0104)
                                              0)))) (show (nb073AlphaDummy090 x y) ≠
                                      (nb073AlphaDummy093 x y) from (by
                                      unfold nb073AlphaDummy093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0105 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from (by
                                        unfold nb073AlphaDummy092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073AlphaDummy090 x y) ≠
                                        (nb073AlphaDummy093 x y) from (by
                                        unfold nb073AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy092), (nb073AlphaDummy093 x y)),
                                    ((nb073AlphaDummy088), (nb073AlphaDummy090 x y)),
                                    ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
                                    ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
                                    ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
                                    ((nb073AlphaDummy086), (nb073AlphaDummy087 x y)),
                                    ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy081) from
                      (by
                        unfold nb073AlphaDummy081;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))))
                    (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy083 x y) from (by
                        unfold nb073AlphaDummy083;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb073_support_mem_0098 x y) 1))))
                    (TAlphaVar.there
                      (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy080) from (by
                          unfold nb073AlphaDummy080;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0096) 0))))
                      (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy082 x y) from (by
                          unfold nb073AlphaDummy082;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))))
                      (TAlphaVar.there
                        (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy086) from (by
                            unfold nb073AlphaDummy086;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0100) 0))))
                        (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy087 x y) from (by
                            unfold nb073AlphaDummy087;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0101 x y) 0))))
                        (TAlphaVar.there
                          (show (nb073AlphaDummy014) ≠ (nb073AlphaDummy084) from (by
                              unfold nb073AlphaDummy084;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0097) 0))))
                          (show (nb073AlphaDummy016 x y) ≠ (nb073AlphaDummy085 x y) from
                            (by
                              unfold nb073AlphaDummy085;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0099 x y) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb073AlphaDummy000))).fv ∪
                                ((Class.cv (nb073AlphaDummy001))).fv) (by decide))
                            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb073AlphaDummy014))).fv ∪
                        ((Class.cv (nb073AlphaDummy015))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb073AlphaDummy016 x y))).fv ∪
                        ((Class.cv (nb073AlphaDummy017 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy088) from (by
                                unfold nb073AlphaDummy088;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0102) 0)))) (show
                              (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy090 x y) from (by
                                unfold nb073AlphaDummy090;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0103 x y) 0))))
                            (TAlphaVar.there
                              (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy089) from (by
                                  unfold nb073AlphaDummy089;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0102) 1)))) (show
                                (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy091 x y) from
                                (by
                                  unfold nb073AlphaDummy091;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0103 x y)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb073AlphaDummy081))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb073AlphaDummy083 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb073AlphaDummy088) ≠ (nb073AlphaDummy095) from (by
          unfold nb073AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 1)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy098 x y) from (by
          unfold nb073AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy094)
        from (by
          unfold nb073AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 0)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy097 x y) from (by
          unfold nb073AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy092)
        from (by
          unfold nb073AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0104)
                  0)))) (show (nb073AlphaDummy090 x y) ≠ (nb073AlphaDummy093 x y) from (by
          unfold nb073AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0105 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy096), (nb073AlphaDummy099 x y)), ((nb073AlphaDummy095),
        (nb073AlphaDummy098 x y)), ((nb073AlphaDummy094), (nb073AlphaDummy097 x y)),
        ((nb073AlphaDummy092), (nb073AlphaDummy093 x y)), ((nb073AlphaDummy088),
        (nb073AlphaDummy090 x y)), ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
        ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)), ((nb073AlphaDummy080),
        (nb073AlphaDummy082 x y)), ((nb073AlphaDummy086), (nb073AlphaDummy087 x y)),
        ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)), ((nb073AlphaDummy015),
        (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
        ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy102) from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy102)
        from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy102) from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy102)
        from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy096), (nb073AlphaDummy099 x y)), ((nb073AlphaDummy095),
        (nb073AlphaDummy098 x y)), ((nb073AlphaDummy094), (nb073AlphaDummy097 x y)),
        ((nb073AlphaDummy092), (nb073AlphaDummy093 x y)), ((nb073AlphaDummy088),
        (nb073AlphaDummy090 x y)), ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
        ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)), ((nb073AlphaDummy080),
        (nb073AlphaDummy082 x y)), ((nb073AlphaDummy086), (nb073AlphaDummy087 x y)),
        ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)), ((nb073AlphaDummy015),
        (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
        ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)), ((nb073AlphaDummy002),
        (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy088))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy090 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy095) ≠
        (nb073AlphaDummy106) from (by
          unfold
            nb073AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy107 x y) from (by
          unfold
            nb073AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy106)
        from (by
          unfold
            nb073AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy107 x y) from (by
          unfold
            nb073AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy108) from (by
          unfold
            nb073AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy109 x y) from (by
          unfold
            nb073AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠
        (nb073AlphaDummy108) from (by
          unfold
            nb073AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy109 x y) from (by
          unfold
            nb073AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from
                                        (by
                                          unfold nb073AlphaDummy092;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0104)
                                                  0)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy093 x y) from (by
                                          unfold nb073AlphaDummy093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0105 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb073AlphaDummy092), (nb073AlphaDummy093 x y)),
                                      ((nb073AlphaDummy088), (nb073AlphaDummy090 x y)),
                                      ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
                                      ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
                                      ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
                                      ((nb073AlphaDummy086), (nb073AlphaDummy087 x y)),
                                      ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
                                      ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                      ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                      ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
                                      ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                      ((nb073AlphaDummy001), y),
                                      ((nb073AlphaDummy000), x), ((nb073AlphaDummy004),
                                        (nb073AlphaDummy005 x y))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from (by
                                        unfold nb073AlphaDummy092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073AlphaDummy090 x y) ≠
                                        (nb073AlphaDummy093 x y) from (by
                                        unfold nb073AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from
                                        (by
                                          unfold nb073AlphaDummy092;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0104)
                                                  0)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy093 x y) from (by
                                          unfold nb073AlphaDummy093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0105 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb073AlphaDummy092), (nb073AlphaDummy093 x y)),
                                      ((nb073AlphaDummy088), (nb073AlphaDummy090 x y)),
                                      ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
                                      ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
                                      ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
                                      ((nb073AlphaDummy086), (nb073AlphaDummy087 x y)),
                                      ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
                                      ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                      ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                      ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
                                      ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                      ((nb073AlphaDummy001), y),
                                      ((nb073AlphaDummy000), x), ((nb073AlphaDummy004),
                                        (nb073AlphaDummy005 x y))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C073C001Part009`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb073_split_alpha_0005`. -/
@[expose]
noncomputable def nb073SplitAlpha0005 (x : Var) (y : Var) :
    TAlphaWff
      [((nb073AlphaDummy112), (nb073AlphaDummy113 x y)),
        ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
        ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
        ((nb073AlphaDummy110), (nb073AlphaDummy111 x y)),
        ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
        ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
        ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
        ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
        ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy112))
          (synCcompl (synCphi (Class.cv (nb073AlphaDummy081))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy112)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073AlphaDummy113 x y))
          (synCcompl (synCphi (Class.cv (nb073AlphaDummy083 x y))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073AlphaDummy113 x y))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy088) from (by
                              unfold nb073AlphaDummy088;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0102) 0))))
                          (show (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy090 x y) from
                            (by
                              unfold nb073AlphaDummy090;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0103 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy089) from (by
                                unfold nb073AlphaDummy089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0102) 1)))) (show
                              (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy091 x y) from (by
                                unfold nb073AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0103 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy114) from (by
                                  unfold nb073AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0132) 0)))) (show
                                (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy115 x y) from
                                (by
                                  unfold nb073AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0133 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy112) from (by
                                    unfold nb073AlphaDummy112;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0130) 0)))) (show
                                  (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy113 x y) from
                                  (by
                                    unfold nb073AlphaDummy113;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0131 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073AlphaDummy081))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073AlphaDummy083 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy095) from (by
          unfold nb073AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 1)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy098 x y) from (by
          unfold nb073AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy088) ≠ (nb073AlphaDummy094) from (by
          unfold nb073AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 0)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy097 x y) from (by
          unfold nb073AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy092)
        from (by
          unfold nb073AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0104) 0)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy093 x y) from (by
          unfold nb073AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0105 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy096), (nb073AlphaDummy099 x y)), ((nb073AlphaDummy095),
        (nb073AlphaDummy098 x y)), ((nb073AlphaDummy094), (nb073AlphaDummy097 x y)),
        ((nb073AlphaDummy092), (nb073AlphaDummy093 x y)), ((nb073AlphaDummy088),
        (nb073AlphaDummy090 x y)), ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
        ((nb073AlphaDummy114), (nb073AlphaDummy115 x y)), ((nb073AlphaDummy112),
        (nb073AlphaDummy113 x y)), ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
        ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)), ((nb073AlphaDummy110),
        (nb073AlphaDummy111 x y)), ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014),
        (nb073AlphaDummy016 x y)), ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy102) from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy102)
        from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy102) from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy102)
        from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy096), (nb073AlphaDummy099 x y)), ((nb073AlphaDummy095),
        (nb073AlphaDummy098 x y)), ((nb073AlphaDummy094), (nb073AlphaDummy097 x y)),
        ((nb073AlphaDummy092), (nb073AlphaDummy093 x y)), ((nb073AlphaDummy088),
        (nb073AlphaDummy090 x y)), ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
        ((nb073AlphaDummy114), (nb073AlphaDummy115 x y)), ((nb073AlphaDummy112),
        (nb073AlphaDummy113 x y)), ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
        ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)), ((nb073AlphaDummy110),
        (nb073AlphaDummy111 x y)), ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014),
        (nb073AlphaDummy016 x y)), ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy088))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy090 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy095) ≠
        (nb073AlphaDummy106) from (by
          unfold
            nb073AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy107 x y) from (by
          unfold
            nb073AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy106)
        from (by
          unfold
            nb073AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy107 x y) from (by
          unfold
            nb073AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy108) from (by
          unfold
            nb073AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy109 x y) from (by
          unfold
            nb073AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠
        (nb073AlphaDummy108) from (by
          unfold
            nb073AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy109 x y) from (by
          unfold
            nb073AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from (by
                                        unfold nb073AlphaDummy092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073AlphaDummy090 x y) ≠
                                        (nb073AlphaDummy093 x y) from (by
                                        unfold nb073AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy092), (nb073AlphaDummy093 x y)),
                                    ((nb073AlphaDummy088), (nb073AlphaDummy090 x y)),
                                    ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
                                    ((nb073AlphaDummy114), (nb073AlphaDummy115 x y)),
                                    ((nb073AlphaDummy112), (nb073AlphaDummy113 x y)),
                                    ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
                                    ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
                                    ((nb073AlphaDummy110), (nb073AlphaDummy111 x y)),
                                    ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from
                                    (by
                                      unfold nb073AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0104)
                                              0)))) (show (nb073AlphaDummy090 x y) ≠
                                      (nb073AlphaDummy093 x y) from (by
                                      unfold nb073AlphaDummy093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0105 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from (by
                                        unfold nb073AlphaDummy092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073AlphaDummy090 x y) ≠
                                        (nb073AlphaDummy093 x y) from (by
                                        unfold nb073AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy092), (nb073AlphaDummy093 x y)),
                                    ((nb073AlphaDummy088), (nb073AlphaDummy090 x y)),
                                    ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
                                    ((nb073AlphaDummy114), (nb073AlphaDummy115 x y)),
                                    ((nb073AlphaDummy112), (nb073AlphaDummy113 x y)),
                                    ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
                                    ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
                                    ((nb073AlphaDummy110), (nb073AlphaDummy111 x y)),
                                    ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy088) from (by
                              unfold nb073AlphaDummy088;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0102) 0))))
                          (show (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy090 x y) from
                            (by
                              unfold nb073AlphaDummy090;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0103 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy089) from (by
                                unfold nb073AlphaDummy089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0102) 1)))) (show
                              (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy091 x y) from (by
                                unfold nb073AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0103 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy114) from (by
                                  unfold nb073AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0132) 0)))) (show
                                (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy115 x y) from
                                (by
                                  unfold nb073AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0133 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073AlphaDummy081) ≠ (nb073AlphaDummy112) from (by
                                    unfold nb073AlphaDummy112;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0130) 0)))) (show
                                  (nb073AlphaDummy083 x y) ≠ (nb073AlphaDummy113 x y) from
                                  (by
                                    unfold nb073AlphaDummy113;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0131 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073AlphaDummy081))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073AlphaDummy083 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy095) from (by
          unfold nb073AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 1)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy098 x y) from (by
          unfold nb073AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y) 1)))) (TAlphaVar.there (show
        (nb073AlphaDummy088) ≠ (nb073AlphaDummy094) from (by
          unfold nb073AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0106) 0)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy097 x y) from (by
          unfold nb073AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0107 x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy092)
        from (by
          unfold nb073AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0104) 0)))) (show (nb073AlphaDummy090 x y) ≠
        (nb073AlphaDummy093 x y) from (by
          unfold nb073AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0105 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy096), (nb073AlphaDummy099 x y)), ((nb073AlphaDummy095),
        (nb073AlphaDummy098 x y)), ((nb073AlphaDummy094), (nb073AlphaDummy097 x y)),
        ((nb073AlphaDummy092), (nb073AlphaDummy093 x y)), ((nb073AlphaDummy088),
        (nb073AlphaDummy090 x y)), ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
        ((nb073AlphaDummy114), (nb073AlphaDummy115 x y)), ((nb073AlphaDummy112),
        (nb073AlphaDummy113 x y)), ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
        ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)), ((nb073AlphaDummy110),
        (nb073AlphaDummy111 x y)), ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014),
        (nb073AlphaDummy016 x y)), ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy102) from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy102)
        from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy102) from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0110)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0111
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0108)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0109
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy102)
        from (by
          unfold
            nb073AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0114)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy103 x y) from (by
          unfold
            nb073AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0115
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy100)
        from (by
          unfold
            nb073AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0112)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy101 x y) from (by
          unfold
            nb073AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0113
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb073AlphaDummy096), (nb073AlphaDummy099 x y)), ((nb073AlphaDummy095),
        (nb073AlphaDummy098 x y)), ((nb073AlphaDummy094), (nb073AlphaDummy097 x y)),
        ((nb073AlphaDummy092), (nb073AlphaDummy093 x y)), ((nb073AlphaDummy088),
        (nb073AlphaDummy090 x y)), ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
        ((nb073AlphaDummy114), (nb073AlphaDummy115 x y)), ((nb073AlphaDummy112),
        (nb073AlphaDummy113 x y)), ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
        ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)), ((nb073AlphaDummy110),
        (nb073AlphaDummy111 x y)), ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
        ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)), ((nb073AlphaDummy014),
        (nb073AlphaDummy016 x y)), ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
        ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)), ((nb073AlphaDummy001), y),
        ((nb073AlphaDummy000), x), ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy088))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073AlphaDummy090 x
        y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy095) ≠
        (nb073AlphaDummy106) from (by
          unfold
            nb073AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy107 x y) from (by
          unfold
            nb073AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy106)
        from (by
          unfold
            nb073AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0118)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy107 x y) from (by
          unfold
            nb073AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0119
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy095) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0116)
                  0)))) (show (nb073AlphaDummy098 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0117
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073AlphaDummy088))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073AlphaDummy090 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy108) from (by
          unfold
            nb073AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy109 x y) from (by
          unfold
            nb073AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073AlphaDummy096) ≠
        (nb073AlphaDummy108) from (by
          unfold
            nb073AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0122)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy109 x y) from (by
          unfold
            nb073AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0123
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy096) ≠ (nb073AlphaDummy104)
        from (by
          unfold
            nb073AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0120)
                  0)))) (show (nb073AlphaDummy099 x y) ≠ (nb073AlphaDummy105 x y) from (by
          unfold
            nb073AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0121
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from (by
                                        unfold nb073AlphaDummy092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073AlphaDummy090 x y) ≠
                                        (nb073AlphaDummy093 x y) from (by
                                        unfold nb073AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy092), (nb073AlphaDummy093 x y)),
                                    ((nb073AlphaDummy088), (nb073AlphaDummy090 x y)),
                                    ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
                                    ((nb073AlphaDummy114), (nb073AlphaDummy115 x y)),
                                    ((nb073AlphaDummy112), (nb073AlphaDummy113 x y)),
                                    ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
                                    ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
                                    ((nb073AlphaDummy110), (nb073AlphaDummy111 x y)),
                                    ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from
                                    (by
                                      unfold nb073AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0104)
                                              0)))) (show (nb073AlphaDummy090 x y) ≠
                                      (nb073AlphaDummy093 x y) from (by
                                      unfold nb073AlphaDummy093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0105 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy088) ≠ (nb073AlphaDummy092) from (by
                                        unfold nb073AlphaDummy092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0104)
                                                0)))) (show (nb073AlphaDummy090 x y) ≠
                                        (nb073AlphaDummy093 x y) from (by
                                        unfold nb073AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0105 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb073AlphaDummy092), (nb073AlphaDummy093 x y)),
                                    ((nb073AlphaDummy088), (nb073AlphaDummy090 x y)),
                                    ((nb073AlphaDummy089), (nb073AlphaDummy091 x y)),
                                    ((nb073AlphaDummy114), (nb073AlphaDummy115 x y)),
                                    ((nb073AlphaDummy112), (nb073AlphaDummy113 x y)),
                                    ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
                                    ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
                                    ((nb073AlphaDummy110), (nb073AlphaDummy111 x y)),
                                    ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
                                    ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
                                    ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
                                    ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
                                    ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                                    ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                                    ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb073AlphaDummy112), (nb073AlphaDummy113 x y)),
            ((nb073AlphaDummy081), (nb073AlphaDummy083 x y)),
            ((nb073AlphaDummy080), (nb073AlphaDummy082 x y)),
            ((nb073AlphaDummy110), (nb073AlphaDummy111 x y)),
            ((nb073AlphaDummy084), (nb073AlphaDummy085 x y)),
            ((nb073AlphaDummy015), (nb073AlphaDummy017 x y)),
            ((nb073AlphaDummy014), (nb073AlphaDummy016 x y)),
            ((nb073AlphaDummy078), (nb073AlphaDummy079 x y)),
            ((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
            ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
            ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_cross`. -/
@[expose]
noncomputable def nominalDfCross (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCcross) (synCmpt2 x (synCvv) y (synCvv) (synCxp (.cv x) (.cv y)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (show (nb073AlphaDummy002) ≠ (nb073AlphaDummy004) from (by
                            unfold nb073AlphaDummy004;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0004) 0))))) (Ne.symm
                        (show (nb073AlphaDummy003 x y) ≠ (nb073AlphaDummy005 x y) from (by
                            unfold nb073AlphaDummy005;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0005 x y) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy004) from (by
                              unfold nb073AlphaDummy004;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0002) 0))))) (Ne.symm
                          (show y ≠ (nb073AlphaDummy005 x y) from (by
                              unfold nb073AlphaDummy005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0003 x y) 0)))))
                        (TAlphaVar.there (Ne.symm
                            (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy004) from (by
                                unfold nb073AlphaDummy004;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0000) 0))))) (Ne.symm
                            (show x ≠ (nb073AlphaDummy005 x y) from (by
                                unfold nb073AlphaDummy005;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0001 x y) 0)))))
                          (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb073SplitAlpha0002 x y dv_x_y)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex
                                      (TAlphaWff.neg (nb073SplitAlpha0003 x y)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb073SplitAlpha0003 x y))))))))))))) (TAlphaWff.conj
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy002) from (by
                              unfold nb073AlphaDummy002;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0006) 0))))
                          (show x ≠ (nb073AlphaDummy003 x y) from (by
                              unfold nb073AlphaDummy003;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0007 x y) 0))))
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.reflOfClosed
                        [((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                          ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                          ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                        (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb073AlphaDummy001) ≠ (nb073AlphaDummy002) from (by
                              unfold nb073AlphaDummy002;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0042) 0))))
                          (show y ≠ (nb073AlphaDummy003 x y) from (by
                              unfold nb073AlphaDummy003;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0043 x y) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb073AlphaDummy002), (nb073AlphaDummy003 x y)),
                          ((nb073AlphaDummy001), y), ((nb073AlphaDummy000), x),
                          ((nb073AlphaDummy004), (nb073AlphaDummy005 x y))]
                        (synCvv) (by simp only [fv_syn_cvv]))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                      (nb073AlphaDummy015) ≠ (nb073AlphaDummy078) from (by
                                        unfold nb073AlphaDummy078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0094)
                                                0))))) (Ne.symm (show
                                      (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy079 x y)
                                      from (by
                                        unfold nb073AlphaDummy079;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0095 x y) 0)))))
                                  (TAlphaVar.there (Ne.symm (show
                                        (nb073AlphaDummy014) ≠ (nb073AlphaDummy078) from
                                        (by
                                          unfold nb073AlphaDummy078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0092)
                                                  0))))) (Ne.symm (show
                                        (nb073AlphaDummy016 x y) ≠
        (nb073AlphaDummy079 x y) from (by
                                          unfold nb073AlphaDummy079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0093 x y) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg
        (TAlphaWff.neg (nb073SplitAlpha0004 x y))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy081) from (by
          unfold
            nb073AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0124)
                  1)))) (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy083 x y) from (by
          unfold
            nb073AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0126
                    x y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy080)
        from (by
          unfold
            nb073AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0124)
                  0)))) (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy082 x y) from (by
          unfold
            nb073AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0126
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy110)
        from (by
          unfold
            nb073AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0128)
                  0)))) (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy111 x y) from (by
          unfold
            nb073AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0129
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy084)
        from (by
          unfold
            nb073AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0125)
                  0)))) (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy085 x y) from (by
          unfold
            nb073AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0127
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy014))).fv ∪
        ((Class.cv (nb073AlphaDummy015))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb073AlphaDummy016 x y))).fv ∪ ((Class.cv (nb073AlphaDummy017 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb073SplitAlpha0005 x y))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy081) from (by
          unfold
            nb073AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0124)
                  1)))) (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy083 x y) from (by
          unfold
            nb073AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0126
                    x y)
                  1)))) (TAlphaVar.there (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy080)
        from (by
          unfold
            nb073AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0124)
                  0)))) (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy082 x y) from (by
          unfold
            nb073AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0126
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy110)
        from (by
          unfold
            nb073AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0128)
                  0)))) (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy111 x y) from (by
          unfold
            nb073AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0129
                    x y)
                  0)))) (TAlphaVar.there (show (nb073AlphaDummy015) ≠ (nb073AlphaDummy084)
        from (by
          unfold
            nb073AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0125)
                  0)))) (show (nb073AlphaDummy017 x y) ≠ (nb073AlphaDummy085 x y) from (by
          unfold
            nb073AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0127
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073AlphaDummy014))).fv ∪
        ((Class.cv (nb073AlphaDummy015))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb073AlphaDummy016 x y))).fv ∪ ((Class.cv (nb073AlphaDummy017 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb073SplitAlpha0005 x y))))))))))))))))) (TAlphaWff.conj (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb073AlphaDummy000))).fv ∪
                                        ((Class.cv (nb073AlphaDummy001))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cv (TAlphaVar.there
                                    (show (nb073AlphaDummy000) ≠ (nb073AlphaDummy015) from
                                      (by
                                        unfold nb073AlphaDummy015;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0014)
                                                1)))) (show x ≠ (nb073AlphaDummy017 x y) from
                                      (by
                                        unfold nb073AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0016 x y) 1))))
                                    (TAlphaVar.there (show
                                        (nb073AlphaDummy000) ≠ (nb073AlphaDummy014) from
                                        (by
                                          unfold nb073AlphaDummy014;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0014)
                                                  0))))
                                      (show x ≠ (nb073AlphaDummy016 x y) from (by
                                          unfold nb073AlphaDummy016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0016 x y) 0))))
                                      (TAlphaVar.there (show (nb073AlphaDummy000) ≠
        (nb073AlphaDummy078) from (by
          unfold nb073AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0134) 0)))) (show x ≠ (nb073AlphaDummy079 x y) from (by
          unfold nb073AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0135 x y) 0)))) (TAlphaVar.there (show
        (nb073AlphaDummy000) ≠ (nb073AlphaDummy002) from (by
          unfold nb073AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0006) 0)))) (show x ≠ (nb073AlphaDummy003 x y) from (by
          unfold nb073AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073AlphaDummy001) ≠ (nb073AlphaDummy015) from (by
                                        unfold nb073AlphaDummy015;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0050)
                                                1)))) (show y ≠ (nb073AlphaDummy017 x y) from
                                      (by
                                        unfold nb073AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0052 x y) 1))))
                                    (TAlphaVar.there (show
                                        (nb073AlphaDummy001) ≠ (nb073AlphaDummy014) from
                                        (by
                                          unfold nb073AlphaDummy014;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0050)
                                                  0))))
                                      (show y ≠ (nb073AlphaDummy016 x y) from (by
                                          unfold nb073AlphaDummy016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0052 x y) 0))))
                                      (TAlphaVar.there (show (nb073AlphaDummy001) ≠
        (nb073AlphaDummy078) from (by
          unfold nb073AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0136) 0)))) (show y ≠ (nb073AlphaDummy079 x y) from (by
          unfold nb073AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0137 x y) 0)))) (TAlphaVar.there (show
        (nb073AlphaDummy001) ≠ (nb073AlphaDummy002) from (by
          unfold nb073AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0042) 0)))) (show y ≠ (nb073AlphaDummy003 x y) from (by
          unfold nb073AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0043 x y) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
