/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block015

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part051`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0020`. -/
@[expose]
noncomputable def nb078SplitAlpha0020 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy199), (nb078AlphaDummy200 f)),
        ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
        ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
        ((nb078AlphaDummy197), (nb078AlphaDummy198 f)),
        ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy199))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy168)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy199)) (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy200 f))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy170 f)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy200 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy175) from (by
                                unfold nb078AlphaDummy175;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0178) 0))))
                            (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy177 f) from (by
                                unfold nb078AlphaDummy177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0179 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy176) from (by
                                  unfold nb078AlphaDummy176;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0178) 1))))
                              (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy178 f) from
                                (by
                                  unfold nb078AlphaDummy178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0179 f) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy201) from (by
                                    unfold nb078AlphaDummy201;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0208) 0)))) (show
                                  (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy202 f) from (by
                                    unfold nb078AlphaDummy202;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0209 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy199) from
                                    (by
                                      unfold nb078AlphaDummy199;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0206)
                                              0)))) (show
                                    (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy200 f) from
                                    (by
                                      unfold nb078AlphaDummy200;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0207 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy168))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy170 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy182) from (by
          unfold nb078AlphaDummy182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 1)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy185 f) from (by
          unfold nb078AlphaDummy185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy181) from (by
          unfold nb078AlphaDummy181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy184 f) from (by
          unfold nb078AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179)
        from (by
          unfold nb078AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0180)
                  0)))) (show (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from (by
          unfold nb078AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy183), (nb078AlphaDummy186 f)), ((nb078AlphaDummy182),
        (nb078AlphaDummy185 f)), ((nb078AlphaDummy181), (nb078AlphaDummy184 f)),
        ((nb078AlphaDummy179), (nb078AlphaDummy180 f)), ((nb078AlphaDummy175),
        (nb078AlphaDummy177 f)), ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
        ((nb078AlphaDummy201), (nb078AlphaDummy202 f)), ((nb078AlphaDummy199),
        (nb078AlphaDummy200 f)), ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
        ((nb078AlphaDummy167), (nb078AlphaDummy169 f)), ((nb078AlphaDummy197),
        (nb078AlphaDummy198 f)), ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy189) from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy189)
        from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy189) from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy189)
        from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy183), (nb078AlphaDummy186 f)), ((nb078AlphaDummy182),
        (nb078AlphaDummy185 f)), ((nb078AlphaDummy181), (nb078AlphaDummy184 f)),
        ((nb078AlphaDummy179), (nb078AlphaDummy180 f)), ((nb078AlphaDummy175),
        (nb078AlphaDummy177 f)), ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
        ((nb078AlphaDummy201), (nb078AlphaDummy202 f)), ((nb078AlphaDummy199),
        (nb078AlphaDummy200 f)), ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
        ((nb078AlphaDummy167), (nb078AlphaDummy169 f)), ((nb078AlphaDummy197),
        (nb078AlphaDummy198 f)), ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy175))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy177
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy182) ≠
        (nb078AlphaDummy193) from (by
          unfold
            nb078AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy194 f) from (by
          unfold
            nb078AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy193)
        from (by
          unfold
            nb078AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy194 f) from (by
          unfold
            nb078AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy195) from (by
          unfold
            nb078AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy196 f) from (by
          unfold
            nb078AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠
        (nb078AlphaDummy195) from (by
          unfold
            nb078AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy196 f) from (by
          unfold
            nb078AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                        (by
                                          unfold nb078AlphaDummy179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0180)
                                                  0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy180 f) from (by
                                          unfold nb078AlphaDummy180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy179), (nb078AlphaDummy180 f)),
                                      ((nb078AlphaDummy175), (nb078AlphaDummy177 f)),
                                      ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
                                      ((nb078AlphaDummy201), (nb078AlphaDummy202 f)),
                                      ((nb078AlphaDummy199), (nb078AlphaDummy200 f)),
                                      ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
                                      ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
                                      ((nb078AlphaDummy197), (nb078AlphaDummy198 f)),
                                      ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
                                        unfold nb078AlphaDummy179;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0180)
                                                0)))) (show (nb078AlphaDummy177 f) ≠
                                        (nb078AlphaDummy180 f) from (by
                                        unfold nb078AlphaDummy180;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                        (by
                                          unfold nb078AlphaDummy179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0180)
                                                  0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy180 f) from (by
                                          unfold nb078AlphaDummy180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy179), (nb078AlphaDummy180 f)),
                                      ((nb078AlphaDummy175), (nb078AlphaDummy177 f)),
                                      ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
                                      ((nb078AlphaDummy201), (nb078AlphaDummy202 f)),
                                      ((nb078AlphaDummy199), (nb078AlphaDummy200 f)),
                                      ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
                                      ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
                                      ((nb078AlphaDummy197), (nb078AlphaDummy198 f)),
                                      ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy175) from (by
                                unfold nb078AlphaDummy175;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0178) 0))))
                            (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy177 f) from (by
                                unfold nb078AlphaDummy177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0179 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy176) from (by
                                  unfold nb078AlphaDummy176;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0178) 1))))
                              (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy178 f) from
                                (by
                                  unfold nb078AlphaDummy178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0179 f) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy201) from (by
                                    unfold nb078AlphaDummy201;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0208) 0)))) (show
                                  (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy202 f) from (by
                                    unfold nb078AlphaDummy202;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0209 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy199) from
                                    (by
                                      unfold nb078AlphaDummy199;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0206)
                                              0)))) (show
                                    (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy200 f) from
                                    (by
                                      unfold nb078AlphaDummy200;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0207 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy168))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy170 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy182) from (by
          unfold nb078AlphaDummy182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 1)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy185 f) from (by
          unfold nb078AlphaDummy185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy181) from (by
          unfold nb078AlphaDummy181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy184 f) from (by
          unfold nb078AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179)
        from (by
          unfold nb078AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0180)
                  0)))) (show (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from (by
          unfold nb078AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy183), (nb078AlphaDummy186 f)), ((nb078AlphaDummy182),
        (nb078AlphaDummy185 f)), ((nb078AlphaDummy181), (nb078AlphaDummy184 f)),
        ((nb078AlphaDummy179), (nb078AlphaDummy180 f)), ((nb078AlphaDummy175),
        (nb078AlphaDummy177 f)), ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
        ((nb078AlphaDummy201), (nb078AlphaDummy202 f)), ((nb078AlphaDummy199),
        (nb078AlphaDummy200 f)), ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
        ((nb078AlphaDummy167), (nb078AlphaDummy169 f)), ((nb078AlphaDummy197),
        (nb078AlphaDummy198 f)), ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy189) from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy189)
        from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy189) from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy189)
        from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy183), (nb078AlphaDummy186 f)), ((nb078AlphaDummy182),
        (nb078AlphaDummy185 f)), ((nb078AlphaDummy181), (nb078AlphaDummy184 f)),
        ((nb078AlphaDummy179), (nb078AlphaDummy180 f)), ((nb078AlphaDummy175),
        (nb078AlphaDummy177 f)), ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
        ((nb078AlphaDummy201), (nb078AlphaDummy202 f)), ((nb078AlphaDummy199),
        (nb078AlphaDummy200 f)), ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
        ((nb078AlphaDummy167), (nb078AlphaDummy169 f)), ((nb078AlphaDummy197),
        (nb078AlphaDummy198 f)), ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy175))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy177
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy182) ≠
        (nb078AlphaDummy193) from (by
          unfold
            nb078AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy194 f) from (by
          unfold
            nb078AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy193)
        from (by
          unfold
            nb078AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy194 f) from (by
          unfold
            nb078AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy195) from (by
          unfold
            nb078AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy196 f) from (by
          unfold
            nb078AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠
        (nb078AlphaDummy195) from (by
          unfold
            nb078AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy196 f) from (by
          unfold
            nb078AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                        (by
                                          unfold nb078AlphaDummy179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0180)
                                                  0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy180 f) from (by
                                          unfold nb078AlphaDummy180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy179), (nb078AlphaDummy180 f)),
                                      ((nb078AlphaDummy175), (nb078AlphaDummy177 f)),
                                      ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
                                      ((nb078AlphaDummy201), (nb078AlphaDummy202 f)),
                                      ((nb078AlphaDummy199), (nb078AlphaDummy200 f)),
                                      ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
                                      ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
                                      ((nb078AlphaDummy197), (nb078AlphaDummy198 f)),
                                      ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
                                        unfold nb078AlphaDummy179;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0180)
                                                0)))) (show (nb078AlphaDummy177 f) ≠
                                        (nb078AlphaDummy180 f) from (by
                                        unfold nb078AlphaDummy180;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                        (by
                                          unfold nb078AlphaDummy179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0180)
                                                  0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy180 f) from (by
                                          unfold nb078AlphaDummy180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy179), (nb078AlphaDummy180 f)),
                                      ((nb078AlphaDummy175), (nb078AlphaDummy177 f)),
                                      ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
                                      ((nb078AlphaDummy201), (nb078AlphaDummy202 f)),
                                      ((nb078AlphaDummy199), (nb078AlphaDummy200 f)),
                                      ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
                                      ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
                                      ((nb078AlphaDummy197), (nb078AlphaDummy198 f)),
                                      ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb078AlphaDummy199), (nb078AlphaDummy200 f)),
            ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
            ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
            ((nb078AlphaDummy197), (nb078AlphaDummy198 f)),
            ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
            ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
            ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
            ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
            ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
            ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part052`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0021`. -/
@[expose]
noncomputable def nb078SplitAlpha0021 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy208), (nb078AlphaDummy210 f)),
        ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
        ((nb078AlphaDummy237), (nb078AlphaDummy238 f)),
        ((nb078AlphaDummy211), (nb078AlphaDummy212 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy208))
          (Class.cv (nb078AlphaDummy203))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy207))
            (synCun (synCphi (Class.cv (nb078AlphaDummy208))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy210 f))
          (Class.cv (nb078AlphaDummy205 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
            (synCun (synCphi (Class.cv (nb078AlphaDummy210 f))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy203) ≠ (nb078AlphaDummy208) from (by
              unfold nb078AlphaDummy208;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 1))))
          (show (nb078AlphaDummy205 f) ≠ (nb078AlphaDummy210 f) from (by
              unfold nb078AlphaDummy210;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 1))))
          (TAlphaVar.there (show (nb078AlphaDummy203) ≠ (nb078AlphaDummy207) from (by
                unfold nb078AlphaDummy207;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 0))))
            (show (nb078AlphaDummy205 f) ≠ (nb078AlphaDummy209 f) from (by
                unfold nb078AlphaDummy209;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 0))))
            (TAlphaVar.there (show (nb078AlphaDummy203) ≠ (nb078AlphaDummy237) from (by
                  unfold nb078AlphaDummy237;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0242) 0))))
              (show (nb078AlphaDummy205 f) ≠ (nb078AlphaDummy238 f) from (by
                  unfold nb078AlphaDummy238;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0243 f) 0))))
              (TAlphaVar.there (show (nb078AlphaDummy203) ≠ (nb078AlphaDummy211) from (by
                    unfold nb078AlphaDummy211;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0239) 0))))
                (show (nb078AlphaDummy205 f) ≠ (nb078AlphaDummy212 f) from (by
                    unfold nb078AlphaDummy212;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0241 f) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((synCcnv (Class.cv (nb078AlphaDummy000)))).fv ∪ ((synCvv)).fv)
                    (by decide))
                  (freshVar_injective (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078AlphaDummy204))).fv ∪
                ((Class.cv (nb078AlphaDummy203))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078AlphaDummy206 f))).fv ∪
                ((Class.cv (nb078AlphaDummy205 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy208) ≠ (nb078AlphaDummy215) from (by
                                        unfold nb078AlphaDummy215;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0216)
                                                0)))) (show (nb078AlphaDummy210 f) ≠
                                        (nb078AlphaDummy217 f) from (by
                                        unfold nb078AlphaDummy217;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0217 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy208) ≠ (nb078AlphaDummy216) from
                                        (by
                                          unfold nb078AlphaDummy216;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0216)
                                                  1)))) (show (nb078AlphaDummy210 f) ≠
        (nb078AlphaDummy218 f) from (by
                                          unfold nb078AlphaDummy218;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0217 f) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy208) ≠
        (nb078AlphaDummy241) from (by
          unfold nb078AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0246) 0)))) (show (nb078AlphaDummy210 f) ≠
        (nb078AlphaDummy242 f) from (by
          unfold nb078AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0247 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy208) ≠ (nb078AlphaDummy239) from (by
          unfold nb078AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0244) 0)))) (show (nb078AlphaDummy210 f) ≠
        (nb078AlphaDummy240 f) from (by
          unfold nb078AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0245 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy208))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy210 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy222) from (by
          unfold nb078AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  1)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy225 f) from (by
          unfold nb078AlphaDummy225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy221)
        from (by
          unfold nb078AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  0)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy224 f) from (by
          unfold nb078AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219)
        from (by
          unfold
            nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218)
                  0)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy220 f) from (by
          unfold
            nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy223), (nb078AlphaDummy226 f)), ((nb078AlphaDummy222),
        (nb078AlphaDummy225 f)), ((nb078AlphaDummy221), (nb078AlphaDummy224 f)),
        ((nb078AlphaDummy219), (nb078AlphaDummy220 f)), ((nb078AlphaDummy215),
        (nb078AlphaDummy217 f)), ((nb078AlphaDummy216), (nb078AlphaDummy218 f)),
        ((nb078AlphaDummy241), (nb078AlphaDummy242 f)), ((nb078AlphaDummy239),
        (nb078AlphaDummy240 f)), ((nb078AlphaDummy208), (nb078AlphaDummy210 f)),
        ((nb078AlphaDummy207), (nb078AlphaDummy209 f)), ((nb078AlphaDummy237),
        (nb078AlphaDummy238 f)), ((nb078AlphaDummy211), (nb078AlphaDummy212 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy223), (nb078AlphaDummy226 f)), ((nb078AlphaDummy222),
        (nb078AlphaDummy225 f)), ((nb078AlphaDummy221), (nb078AlphaDummy224 f)),
        ((nb078AlphaDummy219), (nb078AlphaDummy220 f)), ((nb078AlphaDummy215),
        (nb078AlphaDummy217 f)), ((nb078AlphaDummy216), (nb078AlphaDummy218 f)),
        ((nb078AlphaDummy241), (nb078AlphaDummy242 f)), ((nb078AlphaDummy239),
        (nb078AlphaDummy240 f)), ((nb078AlphaDummy208), (nb078AlphaDummy210 f)),
        ((nb078AlphaDummy207), (nb078AlphaDummy209 f)), ((nb078AlphaDummy237),
        (nb078AlphaDummy238 f)), ((nb078AlphaDummy211), (nb078AlphaDummy212 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy215))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy233) from (by
          unfold
            nb078AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy234 f) from (by
          unfold
            nb078AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy222) ≠
        (nb078AlphaDummy233) from (by
          unfold
            nb078AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy234 f) from (by
          unfold
            nb078AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy235) from (by
          unfold
            nb078AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy236 f) from (by
          unfold
            nb078AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy235) from (by
          unfold
            nb078AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy236 f) from (by
          unfold
            nb078AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219)
        from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy219), (nb078AlphaDummy220 f)),
        ((nb078AlphaDummy215), (nb078AlphaDummy217 f)), ((nb078AlphaDummy216),
        (nb078AlphaDummy218 f)), ((nb078AlphaDummy241), (nb078AlphaDummy242 f)),
        ((nb078AlphaDummy239), (nb078AlphaDummy240 f)), ((nb078AlphaDummy208),
        (nb078AlphaDummy210 f)), ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
        ((nb078AlphaDummy237), (nb078AlphaDummy238 f)), ((nb078AlphaDummy211),
        (nb078AlphaDummy212 f)), ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy219), (nb078AlphaDummy220 f)),
        ((nb078AlphaDummy215), (nb078AlphaDummy217 f)), ((nb078AlphaDummy216),
        (nb078AlphaDummy218 f)), ((nb078AlphaDummy241), (nb078AlphaDummy242 f)),
        ((nb078AlphaDummy239), (nb078AlphaDummy240 f)), ((nb078AlphaDummy208),
        (nb078AlphaDummy210 f)), ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
        ((nb078AlphaDummy237), (nb078AlphaDummy238 f)), ((nb078AlphaDummy211),
        (nb078AlphaDummy212 f)), ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy208) ≠ (nb078AlphaDummy215) from (by
                                        unfold nb078AlphaDummy215;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0216)
                                                0)))) (show (nb078AlphaDummy210 f) ≠
                                        (nb078AlphaDummy217 f) from (by
                                        unfold nb078AlphaDummy217;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0217 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy208) ≠ (nb078AlphaDummy216) from
                                        (by
                                          unfold nb078AlphaDummy216;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0216)
                                                  1)))) (show (nb078AlphaDummy210 f) ≠
        (nb078AlphaDummy218 f) from (by
                                          unfold nb078AlphaDummy218;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0217 f) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy208) ≠
        (nb078AlphaDummy241) from (by
          unfold nb078AlphaDummy241;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0246) 0)))) (show (nb078AlphaDummy210 f) ≠
        (nb078AlphaDummy242 f) from (by
          unfold nb078AlphaDummy242;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0247 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy208) ≠ (nb078AlphaDummy239) from (by
          unfold nb078AlphaDummy239;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0244) 0)))) (show (nb078AlphaDummy210 f) ≠
        (nb078AlphaDummy240 f) from (by
          unfold nb078AlphaDummy240;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0245 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy208))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy210 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy222) from (by
          unfold nb078AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  1)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy225 f) from (by
          unfold nb078AlphaDummy225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy221)
        from (by
          unfold nb078AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  0)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy224 f) from (by
          unfold nb078AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219)
        from (by
          unfold
            nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218)
                  0)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy220 f) from (by
          unfold
            nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy223), (nb078AlphaDummy226 f)), ((nb078AlphaDummy222),
        (nb078AlphaDummy225 f)), ((nb078AlphaDummy221), (nb078AlphaDummy224 f)),
        ((nb078AlphaDummy219), (nb078AlphaDummy220 f)), ((nb078AlphaDummy215),
        (nb078AlphaDummy217 f)), ((nb078AlphaDummy216), (nb078AlphaDummy218 f)),
        ((nb078AlphaDummy241), (nb078AlphaDummy242 f)), ((nb078AlphaDummy239),
        (nb078AlphaDummy240 f)), ((nb078AlphaDummy208), (nb078AlphaDummy210 f)),
        ((nb078AlphaDummy207), (nb078AlphaDummy209 f)), ((nb078AlphaDummy237),
        (nb078AlphaDummy238 f)), ((nb078AlphaDummy211), (nb078AlphaDummy212 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy223), (nb078AlphaDummy226 f)), ((nb078AlphaDummy222),
        (nb078AlphaDummy225 f)), ((nb078AlphaDummy221), (nb078AlphaDummy224 f)),
        ((nb078AlphaDummy219), (nb078AlphaDummy220 f)), ((nb078AlphaDummy215),
        (nb078AlphaDummy217 f)), ((nb078AlphaDummy216), (nb078AlphaDummy218 f)),
        ((nb078AlphaDummy241), (nb078AlphaDummy242 f)), ((nb078AlphaDummy239),
        (nb078AlphaDummy240 f)), ((nb078AlphaDummy208), (nb078AlphaDummy210 f)),
        ((nb078AlphaDummy207), (nb078AlphaDummy209 f)), ((nb078AlphaDummy237),
        (nb078AlphaDummy238 f)), ((nb078AlphaDummy211), (nb078AlphaDummy212 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy215))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy233) from (by
          unfold
            nb078AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy234 f) from (by
          unfold
            nb078AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy222) ≠
        (nb078AlphaDummy233) from (by
          unfold
            nb078AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy234 f) from (by
          unfold
            nb078AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy235) from (by
          unfold
            nb078AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy236 f) from (by
          unfold
            nb078AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy235) from (by
          unfold
            nb078AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy236 f) from (by
          unfold
            nb078AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219)
        from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy219), (nb078AlphaDummy220 f)),
        ((nb078AlphaDummy215), (nb078AlphaDummy217 f)), ((nb078AlphaDummy216),
        (nb078AlphaDummy218 f)), ((nb078AlphaDummy241), (nb078AlphaDummy242 f)),
        ((nb078AlphaDummy239), (nb078AlphaDummy240 f)), ((nb078AlphaDummy208),
        (nb078AlphaDummy210 f)), ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
        ((nb078AlphaDummy237), (nb078AlphaDummy238 f)), ((nb078AlphaDummy211),
        (nb078AlphaDummy212 f)), ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy219), (nb078AlphaDummy220 f)),
        ((nb078AlphaDummy215), (nb078AlphaDummy217 f)), ((nb078AlphaDummy216),
        (nb078AlphaDummy218 f)), ((nb078AlphaDummy241), (nb078AlphaDummy242 f)),
        ((nb078AlphaDummy239), (nb078AlphaDummy240 f)), ((nb078AlphaDummy208),
        (nb078AlphaDummy210 f)), ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
        ((nb078AlphaDummy237), (nb078AlphaDummy238 f)), ((nb078AlphaDummy211),
        (nb078AlphaDummy212 f)), ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy239), (nb078AlphaDummy240 f)),
                    ((nb078AlphaDummy208), (nb078AlphaDummy210 f)),
                    ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
                    ((nb078AlphaDummy237), (nb078AlphaDummy238 f)),
                    ((nb078AlphaDummy211), (nb078AlphaDummy212 f)),
                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part053`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0022`. -/
@[expose]
noncomputable def nb078SplitAlpha0022 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy211), (nb078AlphaDummy212 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy211)) (synCcompl
            (Class.cab (nb078AlphaDummy207)
              (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
                (Wff.classEq (Class.cv (nb078AlphaDummy207))
                  (synCphi (Class.cv (nb078AlphaDummy208)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy211)) (synCcompl
              (Class.cab (nb078AlphaDummy207)
                (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
                  (Wff.classEq (Class.cv (nb078AlphaDummy207))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy212 f)) (synCcompl
            (Class.cab (nb078AlphaDummy209 f)
              (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                  (synCphi (Class.cv (nb078AlphaDummy210 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy212 f)) (synCcompl
              (Class.cab (nb078AlphaDummy209 f)
                (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
                  (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy208) from (by
                              unfold nb078AlphaDummy208;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0210) 1))))
                          (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy210 f) from (by
                              unfold nb078AlphaDummy210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0212 f) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy207) from (by
                                unfold nb078AlphaDummy207;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0210) 0))))
                            (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy209 f) from (by
                                unfold nb078AlphaDummy209;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0212 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy213) from (by
                                  unfold nb078AlphaDummy213;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0214) 0))))
                              (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy214 f) from
                                (by
                                  unfold nb078AlphaDummy214;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0215 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy211) from (by
                                    unfold nb078AlphaDummy211;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0211) 0)))) (show
                                  (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy212 f) from (by
                                    unfold nb078AlphaDummy212;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0213 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy204))).fv ∪
                              ((Class.cv (nb078AlphaDummy203))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy206 f))).fv ∪
                              ((Class.cv (nb078AlphaDummy205 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy208) ≠ (nb078AlphaDummy215) from
                                    (by
                                      unfold nb078AlphaDummy215;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0216)
                                              0)))) (show
                                    (nb078AlphaDummy210 f) ≠ (nb078AlphaDummy217 f) from
                                    (by
                                      unfold nb078AlphaDummy217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0217 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy208) ≠ (nb078AlphaDummy216) from (by
                                        unfold nb078AlphaDummy216;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0216)
                                                1)))) (show (nb078AlphaDummy210 f) ≠
                                        (nb078AlphaDummy218 f) from (by
                                        unfold nb078AlphaDummy218;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0217 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy208))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy210 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy215) ≠ (nb078AlphaDummy222) from (by
          unfold nb078AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  1)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy225 f) from (by
          unfold nb078AlphaDummy225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy221)
        from (by
          unfold nb078AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  0)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy224 f) from (by
          unfold nb078AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219)
        from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218)
                  0)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy223), (nb078AlphaDummy226 f)), ((nb078AlphaDummy222),
        (nb078AlphaDummy225 f)), ((nb078AlphaDummy221), (nb078AlphaDummy224 f)),
        ((nb078AlphaDummy219), (nb078AlphaDummy220 f)), ((nb078AlphaDummy215),
        (nb078AlphaDummy217 f)), ((nb078AlphaDummy216), (nb078AlphaDummy218 f)),
        ((nb078AlphaDummy208), (nb078AlphaDummy210 f)), ((nb078AlphaDummy207),
        (nb078AlphaDummy209 f)), ((nb078AlphaDummy213), (nb078AlphaDummy214 f)),
        ((nb078AlphaDummy211), (nb078AlphaDummy212 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy223), (nb078AlphaDummy226 f)), ((nb078AlphaDummy222),
        (nb078AlphaDummy225 f)), ((nb078AlphaDummy221), (nb078AlphaDummy224 f)),
        ((nb078AlphaDummy219), (nb078AlphaDummy220 f)), ((nb078AlphaDummy215),
        (nb078AlphaDummy217 f)), ((nb078AlphaDummy216), (nb078AlphaDummy218 f)),
        ((nb078AlphaDummy208), (nb078AlphaDummy210 f)), ((nb078AlphaDummy207),
        (nb078AlphaDummy209 f)), ((nb078AlphaDummy213), (nb078AlphaDummy214 f)),
        ((nb078AlphaDummy211), (nb078AlphaDummy212 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy215))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy233) from (by
          unfold
            nb078AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy234 f) from (by
          unfold
            nb078AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy222) ≠
        (nb078AlphaDummy233) from (by
          unfold
            nb078AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy234 f) from (by
          unfold
            nb078AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy235) from (by
          unfold
            nb078AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy236 f) from (by
          unfold
            nb078AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy235) from (by
          unfold
            nb078AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy236 f) from (by
          unfold
            nb078AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy215) ≠ (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy219),
        (nb078AlphaDummy220 f)), ((nb078AlphaDummy215), (nb078AlphaDummy217 f)),
        ((nb078AlphaDummy216), (nb078AlphaDummy218 f)), ((nb078AlphaDummy208),
        (nb078AlphaDummy210 f)), ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
        ((nb078AlphaDummy213), (nb078AlphaDummy214 f)), ((nb078AlphaDummy211),
        (nb078AlphaDummy212 f)), ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy215) ≠
        (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy215) ≠ (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy219),
        (nb078AlphaDummy220 f)), ((nb078AlphaDummy215), (nb078AlphaDummy217 f)),
        ((nb078AlphaDummy216), (nb078AlphaDummy218 f)), ((nb078AlphaDummy208),
        (nb078AlphaDummy210 f)), ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
        ((nb078AlphaDummy213), (nb078AlphaDummy214 f)), ((nb078AlphaDummy211),
        (nb078AlphaDummy212 f)), ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy208) from (by
                              unfold nb078AlphaDummy208;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0210) 1))))
                          (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy210 f) from (by
                              unfold nb078AlphaDummy210;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0212 f) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy207) from (by
                                unfold nb078AlphaDummy207;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0210) 0))))
                            (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy209 f) from (by
                                unfold nb078AlphaDummy209;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0212 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy213) from (by
                                  unfold nb078AlphaDummy213;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0214) 0))))
                              (show (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy214 f) from
                                (by
                                  unfold nb078AlphaDummy214;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0215 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy204) ≠ (nb078AlphaDummy211) from (by
                                    unfold nb078AlphaDummy211;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0211) 0)))) (show
                                  (nb078AlphaDummy206 f) ≠ (nb078AlphaDummy212 f) from (by
                                    unfold nb078AlphaDummy212;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0213 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy204))).fv ∪
                              ((Class.cv (nb078AlphaDummy203))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy206 f))).fv ∪
                              ((Class.cv (nb078AlphaDummy205 f))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy208) ≠ (nb078AlphaDummy215) from
                                    (by
                                      unfold nb078AlphaDummy215;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0216)
                                              0)))) (show
                                    (nb078AlphaDummy210 f) ≠ (nb078AlphaDummy217 f) from
                                    (by
                                      unfold nb078AlphaDummy217;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0217 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy208) ≠ (nb078AlphaDummy216) from (by
                                        unfold nb078AlphaDummy216;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0216)
                                                1)))) (show (nb078AlphaDummy210 f) ≠
                                        (nb078AlphaDummy218 f) from (by
                                        unfold nb078AlphaDummy218;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0217 f)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy208))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy210 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy215) ≠ (nb078AlphaDummy222) from (by
          unfold nb078AlphaDummy222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  1)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy225 f) from (by
          unfold nb078AlphaDummy225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy221)
        from (by
          unfold nb078AlphaDummy221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0220)
                  0)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy224 f) from (by
          unfold nb078AlphaDummy224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0221
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy215) ≠ (nb078AlphaDummy219)
        from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218)
                  0)))) (show (nb078AlphaDummy217 f) ≠ (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy223), (nb078AlphaDummy226 f)), ((nb078AlphaDummy222),
        (nb078AlphaDummy225 f)), ((nb078AlphaDummy221), (nb078AlphaDummy224 f)),
        ((nb078AlphaDummy219), (nb078AlphaDummy220 f)), ((nb078AlphaDummy215),
        (nb078AlphaDummy217 f)), ((nb078AlphaDummy216), (nb078AlphaDummy218 f)),
        ((nb078AlphaDummy208), (nb078AlphaDummy210 f)), ((nb078AlphaDummy207),
        (nb078AlphaDummy209 f)), ((nb078AlphaDummy213), (nb078AlphaDummy214 f)),
        ((nb078AlphaDummy211), (nb078AlphaDummy212 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0224)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0225
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0222)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0223
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy229) from (by
          unfold
            nb078AlphaDummy229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0228)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy230 f) from (by
          unfold
            nb078AlphaDummy230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0229
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy227)
        from (by
          unfold
            nb078AlphaDummy227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0226)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy228 f) from (by
          unfold
            nb078AlphaDummy228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0227
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy223), (nb078AlphaDummy226 f)), ((nb078AlphaDummy222),
        (nb078AlphaDummy225 f)), ((nb078AlphaDummy221), (nb078AlphaDummy224 f)),
        ((nb078AlphaDummy219), (nb078AlphaDummy220 f)), ((nb078AlphaDummy215),
        (nb078AlphaDummy217 f)), ((nb078AlphaDummy216), (nb078AlphaDummy218 f)),
        ((nb078AlphaDummy208), (nb078AlphaDummy210 f)), ((nb078AlphaDummy207),
        (nb078AlphaDummy209 f)), ((nb078AlphaDummy213), (nb078AlphaDummy214 f)),
        ((nb078AlphaDummy211), (nb078AlphaDummy212 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy217 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy215))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy233) from (by
          unfold
            nb078AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy234 f) from (by
          unfold
            nb078AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy222) ≠
        (nb078AlphaDummy233) from (by
          unfold
            nb078AlphaDummy233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0232)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy234 f) from (by
          unfold
            nb078AlphaDummy234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0233
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy222) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0230)
                  0)))) (show (nb078AlphaDummy225 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0231
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy215))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy217 f))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy235) from (by
          unfold
            nb078AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy236 f) from (by
          unfold
            nb078AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy223) ≠
        (nb078AlphaDummy235) from (by
          unfold
            nb078AlphaDummy235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0236)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy236 f) from (by
          unfold
            nb078AlphaDummy236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0237
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy223) ≠ (nb078AlphaDummy231)
        from (by
          unfold
            nb078AlphaDummy231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0234)
                  0)))) (show (nb078AlphaDummy226 f) ≠ (nb078AlphaDummy232 f) from (by
          unfold
            nb078AlphaDummy232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0235
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy215) ≠ (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy219),
        (nb078AlphaDummy220 f)), ((nb078AlphaDummy215), (nb078AlphaDummy217 f)),
        ((nb078AlphaDummy216), (nb078AlphaDummy218 f)), ((nb078AlphaDummy208),
        (nb078AlphaDummy210 f)), ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
        ((nb078AlphaDummy213), (nb078AlphaDummy214 f)), ((nb078AlphaDummy211),
        (nb078AlphaDummy212 f)), ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy215) ≠
        (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy215) ≠ (nb078AlphaDummy219) from (by
          unfold nb078AlphaDummy219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0218) 0)))) (show (nb078AlphaDummy217 f) ≠
        (nb078AlphaDummy220 f) from (by
          unfold nb078AlphaDummy220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0219 f) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy219),
        (nb078AlphaDummy220 f)), ((nb078AlphaDummy215), (nb078AlphaDummy217 f)),
        ((nb078AlphaDummy216), (nb078AlphaDummy218 f)), ((nb078AlphaDummy208),
        (nb078AlphaDummy210 f)), ((nb078AlphaDummy207), (nb078AlphaDummy209 f)),
        ((nb078AlphaDummy213), (nb078AlphaDummy214 f)), ((nb078AlphaDummy211),
        (nb078AlphaDummy212 f)), ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0021 x y f)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0021 x y f)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
