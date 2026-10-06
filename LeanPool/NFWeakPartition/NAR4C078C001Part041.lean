/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block012

/-! NF weak partition development: NAR4C078C001Part041. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0009`. -/
@[expose]
noncomputable def nb078SplitAlpha0009 (x : Var) (y : Var) (f : Var) :
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
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.classMem (Class.cv (nb078AlphaDummy199))
        (synCcompl (synCphi (Class.cv (nb078AlphaDummy168)))))
      (Wff.classMem (Class.cv (nb078AlphaDummy200 f))
        (synCcompl (synCphi (Class.cv (nb078AlphaDummy170 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
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
                          (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy178 f) from (by
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
                                      (mem_lt_freshVar (nb078_support_mem_0208) 0))))
                            (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy202 f) from (by
                                unfold nb078AlphaDummy202;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0209 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy199) from (by
                                  unfold nb078AlphaDummy199;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0206) 0))))
                              (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy200 f) from
                                (by
                                  unfold nb078AlphaDummy200;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0207 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078AlphaDummy168))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078AlphaDummy170 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy175) ≠
        (nb078AlphaDummy182) from (by
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
                  (nb078_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
          unfold nb078AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0180) 0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy180 f) from (by
          unfold nb078AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0181 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy007),
        (nb078AlphaDummy008 f)), ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy007),
        (nb078AlphaDummy008 f)), ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy175))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy193) from (by
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
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                    (by
                                      unfold nb078AlphaDummy179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0180)
                                              0)))) (show
                                    (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from
                                    (by
                                      unfold nb078AlphaDummy180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
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
                                  ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                  ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                  ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
                                    unfold nb078AlphaDummy179;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0180) 0)))) (show
                                  (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from (by
                                    unfold nb078AlphaDummy180;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0181 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                    (by
                                      unfold nb078AlphaDummy179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0180)
                                              0)))) (show
                                    (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from
                                    (by
                                      unfold nb078AlphaDummy180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
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
                                  ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                  ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                  ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
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
                          (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy178 f) from (by
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
                                      (mem_lt_freshVar (nb078_support_mem_0208) 0))))
                            (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy202 f) from (by
                                unfold nb078AlphaDummy202;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0209 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy199) from (by
                                  unfold nb078AlphaDummy199;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0206) 0))))
                              (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy200 f) from
                                (by
                                  unfold nb078AlphaDummy200;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0207 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078AlphaDummy168))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078AlphaDummy170 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy175) ≠
        (nb078AlphaDummy182) from (by
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
                  (nb078_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
          unfold nb078AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0180) 0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy180 f) from (by
          unfold nb078AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0181 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy007),
        (nb078AlphaDummy008 f)), ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy007),
        (nb078AlphaDummy008 f)), ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy175))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy193) from (by
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
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                    (by
                                      unfold nb078AlphaDummy179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0180)
                                              0)))) (show
                                    (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from
                                    (by
                                      unfold nb078AlphaDummy180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
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
                                  ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                  ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                  ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
                                    unfold nb078AlphaDummy179;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0180) 0)))) (show
                                  (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from (by
                                    unfold nb078AlphaDummy180;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0181 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                    (by
                                      unfold nb078AlphaDummy179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0180)
                                              0)))) (show
                                    (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from
                                    (by
                                      unfold nb078AlphaDummy180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
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
                                  ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                                  ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                                  ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0010`. -/
@[expose]
noncomputable def nb078SplitAlpha0010 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy015))
          (synCop (Class.cv (nb078AlphaDummy009)) (Class.cv (nb078AlphaDummy010))))
        (Wff.neg (synWex (nb078AlphaDummy011) (synWa
              (synWbr (Class.cv (nb078AlphaDummy009))
                (synCcnv (Class.cv (nb078AlphaDummy000)))
                (Class.cv (nb078AlphaDummy011))) (synWbr (Class.cv (nb078AlphaDummy011))
                (Class.cv (nb078AlphaDummy000)) (Class.cv (nb078AlphaDummy010)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy016 f))
          (synCop (Class.cv (nb078AlphaDummy012 f)) (Class.cv (nb078AlphaDummy013 f))))
        (Wff.neg (synWex (nb078AlphaDummy014 f) (synWa
              (synWbr (Class.cv (nb078AlphaDummy012 f)) (synCcnv (Class.cv f))
                (Class.cv (nb078AlphaDummy014 f)))
              (synWbr (Class.cv (nb078AlphaDummy014 f)) (Class.cv f)
                (Class.cv (nb078AlphaDummy013 f))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy015) from (by
                unfold nb078AlphaDummy015;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0002) 0))))) (Ne.symm
            (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy016 f) from (by
                unfold nb078AlphaDummy016;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0003 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy015) from
                (by
                  unfold nb078AlphaDummy015;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0000) 0)))))
            (Ne.symm (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy016 f) from (by
                  unfold nb078AlphaDummy016;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0001 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0000 x y f)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy018) from
                                    (by
                                      unfold nb078AlphaDummy018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0032)
                                              1)))) (show
                                    (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy020 f) from
                                    (by
                                      unfold nb078AlphaDummy020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0034 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy010) ≠ (nb078AlphaDummy017) from (by
                                        unfold nb078AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0032)
                                                0)))) (show (nb078AlphaDummy013 f) ≠
                                        (nb078AlphaDummy019 f) from (by
                                        unfold nb078AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0034 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy010) ≠ (nb078AlphaDummy047) from
                                        (by
                                          unfold nb078AlphaDummy047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0036)
                                                  0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy048 f) from (by
                                          unfold nb078AlphaDummy048;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0037 f) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy010) ≠
        (nb078AlphaDummy021) from (by
          unfold nb078AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0033) 0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy022 f) from (by
          unfold nb078AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0035 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy009))).fv ∪
                                      ((Class.cv (nb078AlphaDummy010))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy012 f))).fv ∪
                                      ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0001 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy018) from
                                    (by
                                      unfold nb078AlphaDummy018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0032)
                                              1)))) (show
                                    (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy020 f) from
                                    (by
                                      unfold nb078AlphaDummy020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0034 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy010) ≠ (nb078AlphaDummy017) from (by
                                        unfold nb078AlphaDummy017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0032)
                                                0)))) (show (nb078AlphaDummy013 f) ≠
                                        (nb078AlphaDummy019 f) from (by
                                        unfold nb078AlphaDummy019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0034 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy010) ≠ (nb078AlphaDummy047) from
                                        (by
                                          unfold nb078AlphaDummy047;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0036)
                                                  0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy048 f) from (by
                                          unfold nb078AlphaDummy048;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0037 f) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy010) ≠
        (nb078AlphaDummy021) from (by
          unfold nb078AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0033) 0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy022 f) from (by
          unfold nb078AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0035 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy009))).fv ∪
                                      ((Class.cv (nb078AlphaDummy010))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy012 f))).fv ∪
                                      ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0001 x y f)))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0002 x y f)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy011) ≠
        (nb078AlphaDummy054) from (by
          unfold nb078AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 1)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy056 f) from (by
          unfold nb078AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy011) ≠ (nb078AlphaDummy053) from (by
          unfold nb078AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 0)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy055 f) from (by
          unfold nb078AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy011) ≠ (nb078AlphaDummy083) from (by
          unfold nb078AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0074) 0)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy084 f) from (by
          unfold nb078AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0075 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy011) ≠ (nb078AlphaDummy057) from (by
          unfold nb078AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0071) 0)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy058 f) from (by
          unfold nb078AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0073 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy012 f))).fv ∪
        ((Class.cv (nb078AlphaDummy014 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0003 x y f)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy085), (nb078AlphaDummy086 f)), ((nb078AlphaDummy054),
        (nb078AlphaDummy056 f)), ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
        ((nb078AlphaDummy083), (nb078AlphaDummy084 f)), ((nb078AlphaDummy057),
        (nb078AlphaDummy058 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy011) ≠
        (nb078AlphaDummy054) from (by
          unfold nb078AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 1)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy056 f) from (by
          unfold nb078AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy011) ≠ (nb078AlphaDummy053) from (by
          unfold nb078AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 0)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy055 f) from (by
          unfold nb078AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy011) ≠ (nb078AlphaDummy083) from (by
          unfold nb078AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0074) 0)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy084 f) from (by
          unfold nb078AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0075 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy011) ≠ (nb078AlphaDummy057) from (by
          unfold nb078AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0071) 0)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy058 f) from (by
          unfold nb078AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0073 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy012 f))).fv ∪
        ((Class.cv (nb078AlphaDummy014 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0003 x y f)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy085), (nb078AlphaDummy086 f)), ((nb078AlphaDummy054),
        (nb078AlphaDummy056 f)), ((nb078AlphaDummy053), (nb078AlphaDummy055 f)),
        ((nb078AlphaDummy083), (nb078AlphaDummy084 f)), ((nb078AlphaDummy057),
        (nb078AlphaDummy058 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy093) from (by
                                unfold nb078AlphaDummy093;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0082) 0))))) (Ne.symm
                            (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy094 f) from (by
                                unfold nb078AlphaDummy094;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0083 f) 0)))))
                          (TAlphaVar.there (Ne.symm
                              (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy093) from (by
                                  unfold nb078AlphaDummy093;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0080) 0)))))
                            (Ne.symm (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy094 f)
                                from (by
                                  unfold nb078AlphaDummy094;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0081 f) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0004 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy096) from (by
          unfold nb078AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy098 f) from (by
          unfold nb078AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy095)
        from (by
          unfold nb078AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold nb078AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy125)
        from (by
          unfold nb078AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy126 f) from (by
          unfold nb078AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy099)
        from (by
          unfold nb078AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy100 f) from (by
          unfold nb078AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy089))).fv ∪
        ((Class.cv (nb078AlphaDummy090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0005 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy127), (nb078AlphaDummy128 f)), ((nb078AlphaDummy096),
        (nb078AlphaDummy098 f)), ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
        ((nb078AlphaDummy125), (nb078AlphaDummy126 f)), ((nb078AlphaDummy099),
        (nb078AlphaDummy100 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy096) from (by
          unfold nb078AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy098 f) from (by
          unfold nb078AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy095)
        from (by
          unfold nb078AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold nb078AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy125)
        from (by
          unfold nb078AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy126 f) from (by
          unfold nb078AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy099)
        from (by
          unfold nb078AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy100 f) from (by
          unfold nb078AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy089))).fv ∪
        ((Class.cv (nb078AlphaDummy090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0005 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy127), (nb078AlphaDummy128 f)), ((nb078AlphaDummy096),
        (nb078AlphaDummy098 f)), ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
        ((nb078AlphaDummy125), (nb078AlphaDummy126 f)), ((nb078AlphaDummy099),
        (nb078AlphaDummy100 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0006 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy132) from (by
          unfold nb078AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy134 f) from (by
          unfold nb078AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy131)
        from (by
          unfold nb078AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold nb078AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy161)
        from (by
          unfold nb078AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy162 f) from (by
          unfold nb078AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy135)
        from (by
          unfold nb078AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy136 f) from (by
          unfold nb078AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy090))).fv ∪
        ((Class.cv (nb078AlphaDummy089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0007 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy163), (nb078AlphaDummy164 f)), ((nb078AlphaDummy132),
        (nb078AlphaDummy134 f)), ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
        ((nb078AlphaDummy161), (nb078AlphaDummy162 f)), ((nb078AlphaDummy135),
        (nb078AlphaDummy136 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy132) from (by
          unfold nb078AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy134 f) from (by
          unfold nb078AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy131)
        from (by
          unfold nb078AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold nb078AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy161)
        from (by
          unfold nb078AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy162 f) from (by
          unfold nb078AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy135)
        from (by
          unfold nb078AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy136 f) from (by
          unfold nb078AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy090))).fv ∪
        ((Class.cv (nb078AlphaDummy089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0007 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy163), (nb078AlphaDummy164 f)), ((nb078AlphaDummy132),
        (nb078AlphaDummy134 f)), ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
        ((nb078AlphaDummy161), (nb078AlphaDummy162 f)), ((nb078AlphaDummy135),
        (nb078AlphaDummy136 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                          (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy090) from (by
                              unfold nb078AlphaDummy090;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0170) 1))))
                          (show f ≠ (nb078AlphaDummy092 f) from (by
                              unfold nb078AlphaDummy092;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0171 f) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy089) from (by
                                unfold nb078AlphaDummy089;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0170) 0))))
                            (show f ≠ (nb078AlphaDummy091 f) from (by
                                unfold nb078AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0171 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy093) from (by
                                  unfold nb078AlphaDummy093;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0168) 0))))
                              (show f ≠ (nb078AlphaDummy094 f) from (by
                                  unfold nb078AlphaDummy094;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0169 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy011) from (by
                                    unfold nb078AlphaDummy011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0164) 2))))
                                (show f ≠ (nb078AlphaDummy014 f) from (by
                                    unfold nb078AlphaDummy014;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0166 f)
                                            2)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy010) from
                                    (by
                                      unfold nb078AlphaDummy010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0164)
                                              1)))) (show f ≠ (nb078AlphaDummy013 f) from (by
                                      unfold nb078AlphaDummy013;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0166 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy000) ≠ (nb078AlphaDummy009) from (by
                                        unfold nb078AlphaDummy009;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0164)
                                                0)))) (show f ≠ (nb078AlphaDummy012 f) from
                                      (by
                                        unfold nb078AlphaDummy012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0166 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy000) ≠ (nb078AlphaDummy015) from
                                        (by
                                          unfold nb078AlphaDummy015;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0165)
                                                  0)))) (show f ≠ (nb078AlphaDummy016 f) from
                                        (by
                                          unfold nb078AlphaDummy016;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0167 f) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy000) ≠
        (nb078AlphaDummy007) from (by
          unfold nb078AlphaDummy007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0162) 0)))) (show f ≠ (nb078AlphaDummy008 f) from (by
          unfold nb078AlphaDummy008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy000) ≠ (nb078AlphaDummy005) from (by
          unfold nb078AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0160) 0)))) (show f ≠ (nb078AlphaDummy006 f) from (by
          unfold nb078AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0161 f) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0008 x y f)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy010) ≠
        (nb078AlphaDummy168) from (by
          unfold nb078AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 1)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy170 f) from (by
          unfold nb078AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy010) ≠ (nb078AlphaDummy167) from (by
          unfold nb078AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy169 f) from (by
          unfold nb078AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy010) ≠ (nb078AlphaDummy197) from (by
          unfold nb078AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0204) 0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy198 f) from (by
          unfold nb078AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0205 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy010) ≠ (nb078AlphaDummy171) from (by
          unfold nb078AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0201) 0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy172 f) from (by
          unfold nb078AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0203 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb078AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy014 f))).fv ∪
        ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0009 x y f)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy199), (nb078AlphaDummy200 f)), ((nb078AlphaDummy168),
        (nb078AlphaDummy170 f)), ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
        ((nb078AlphaDummy197), (nb078AlphaDummy198 f)), ((nb078AlphaDummy171),
        (nb078AlphaDummy172 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy010) ≠
        (nb078AlphaDummy168) from (by
          unfold nb078AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 1)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy170 f) from (by
          unfold nb078AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy010) ≠ (nb078AlphaDummy167) from (by
          unfold nb078AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy169 f) from (by
          unfold nb078AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy010) ≠ (nb078AlphaDummy197) from (by
          unfold nb078AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0204) 0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy198 f) from (by
          unfold nb078AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0205 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy010) ≠ (nb078AlphaDummy171) from (by
          unfold nb078AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0201) 0)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy172 f) from (by
          unfold nb078AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0203 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb078AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy014 f))).fv ∪
        ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0009 x y f)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy199), (nb078AlphaDummy200 f)), ((nb078AlphaDummy168),
        (nb078AlphaDummy170 f)), ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
        ((nb078AlphaDummy197), (nb078AlphaDummy198 f)), ((nb078AlphaDummy171),
        (nb078AlphaDummy172 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy007), (nb078AlphaDummy008 f)), ((nb078AlphaDummy005),
        (nb078AlphaDummy006 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy011) from (by
                    unfold nb078AlphaDummy011;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0164) 2))))
                (show f ≠ (nb078AlphaDummy014 f) from (by
                    unfold nb078AlphaDummy014;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0166 f) 2))))
                (TAlphaVar.there (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy010) from
                    (by
                      unfold nb078AlphaDummy010;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0164) 1))))
                  (show f ≠ (nb078AlphaDummy013 f) from (by
                      unfold nb078AlphaDummy013;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0166 f) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy009) from
                      (by
                        unfold nb078AlphaDummy009;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0164) 0))))
                    (show f ≠ (nb078AlphaDummy012 f) from (by
                        unfold nb078AlphaDummy012;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0166 f) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy015) from (by
                          unfold nb078AlphaDummy015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0165) 0))))
                      (show f ≠ (nb078AlphaDummy016 f) from (by
                          unfold nb078AlphaDummy016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0167 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy007) from (by
                            unfold nb078AlphaDummy007;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0162) 0))))
                        (show f ≠ (nb078AlphaDummy008 f) from (by
                            unfold nb078AlphaDummy008;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0163 f) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy005) from (by
                              unfold nb078AlphaDummy005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0160) 0))))
                          (show f ≠ (nb078AlphaDummy006 f) from (by
                              unfold nb078AlphaDummy006;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0161 f) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

theorem nb078_wpp_notmem_0506 : (nb078AlphaDummy007) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy007, fv_syn_cid] using (nb078_compact_fv_empty_0026)

theorem nb078_wpp_notmem_0507 (f : Var) : (nb078AlphaDummy008 f) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy008, fv_syn_cid] using (nb078_compact_fv_empty_0027 f)

theorem nb078_wpp_notmem_0508 : (nb078AlphaDummy005) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy005, fv_syn_cid] using (nb078_compact_fv_empty_0028)

theorem nb078_wpp_notmem_0509 (f : Var) : (nb078AlphaDummy006 f) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy006, fv_syn_cid] using (nb078_compact_fv_empty_0029 f)

theorem nb078_wpp_notmem_0510 : (nb078AlphaDummy000) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy000, fv_syn_cid] using (nb078_compact_fv_empty_0030)

theorem nb078_wpp_notmem_0511 (f : Var) : f ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0031 f)

theorem nb078_wpp_notmem_0512 : (nb078AlphaDummy004) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy004, fv_syn_cid] using (nb078_compact_fv_empty_0032)

theorem nb078_wpp_notmem_0513 (y : Var) : y ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0033 y)

theorem nb078_wpp_notmem_0514 : (nb078AlphaDummy003) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy003, fv_syn_cid] using (nb078_compact_fv_empty_0034)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
