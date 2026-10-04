/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C067C001Part009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part010`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0000`. -/
@[expose]
noncomputable def nb067SplitAlpha0000 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy031), (nb067AlphaDummy034 x y)),
        ((nb067AlphaDummy030), (nb067AlphaDummy033 x y)),
        ((nb067AlphaDummy029), (nb067AlphaDummy032 x y)),
        ((nb067AlphaDummy027), (nb067AlphaDummy028 x y)),
        ((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
        ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
        ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
        ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
        ((nb067AlphaDummy021), (nb067AlphaDummy022 x y)),
        ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy029))
            (synCun (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy032 x y))
            (synCun (Class.cv (nb067AlphaDummy033 x y))
              (Class.cv (nb067AlphaDummy034 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy031), (nb067AlphaDummy034 x y)),
          ((nb067AlphaDummy030), (nb067AlphaDummy033 x y)),
          ((nb067AlphaDummy029), (nb067AlphaDummy032 x y)),
          ((nb067AlphaDummy027), (nb067AlphaDummy028 x y)),
          ((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
          ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
          ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
          ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
          ((nb067AlphaDummy021), (nb067AlphaDummy022 x y)),
          ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
          ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
          ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
          ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
          ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0001`. -/
@[expose]
noncomputable def nb067SplitAlpha0001 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
        ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
        ((nb067AlphaDummy021), (nb067AlphaDummy022 x y)),
        ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy015))
        (synCphi (Class.cv (nb067AlphaDummy016))))
      (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
        (synCphi (Class.cv (nb067AlphaDummy018 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv)
          (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb067AlphaDummy016))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb067AlphaDummy018 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0024) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0025 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0024) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0025 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0022) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed [((nb067AlphaDummy031),
                                        (nb067AlphaDummy034 x y)), ((nb067AlphaDummy030),
                                        (nb067AlphaDummy033 x y)), ((nb067AlphaDummy029),
                                        (nb067AlphaDummy032 x y)), ((nb067AlphaDummy027),
                                        (nb067AlphaDummy028 x y)), ((nb067AlphaDummy023),
                                        (nb067AlphaDummy025 x y)), ((nb067AlphaDummy024),
                                        (nb067AlphaDummy026 x y)), ((nb067AlphaDummy016),
                                        (nb067AlphaDummy018 x y)), ((nb067AlphaDummy015),
                                        (nb067AlphaDummy017 x y)), ((nb067AlphaDummy021),
                                        (nb067AlphaDummy022 x y)), ((nb067AlphaDummy019),
                                        (nb067AlphaDummy020 x y)), ((nb067AlphaDummy008),
                                        (nb067AlphaDummy010 x y f)),
                                      ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                                      ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                                      ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                                      ((nb067AlphaDummy002), y),
                                      ((nb067AlphaDummy001), x), ((nb067AlphaDummy005),
                                        (nb067AlphaDummy006 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb067SplitAlpha0000 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy027), (nb067AlphaDummy028 x y)),
                          ((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
                          ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
                          ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
                          ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
                          ((nb067AlphaDummy021), (nb067AlphaDummy022 x y)),
                          ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
                          ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                          ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                          ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                          ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy027), (nb067AlphaDummy028 x y)),
                          ((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
                          ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
                          ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
                          ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
                          ((nb067AlphaDummy021), (nb067AlphaDummy022 x y)),
                          ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
                          ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                          ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                          ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                          ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0002`. -/
@[expose]
noncomputable def nb067SplitAlpha0002 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy031), (nb067AlphaDummy034 x y)),
        ((nb067AlphaDummy030), (nb067AlphaDummy033 x y)),
        ((nb067AlphaDummy029), (nb067AlphaDummy032 x y)),
        ((nb067AlphaDummy027), (nb067AlphaDummy028 x y)),
        ((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
        ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
        ((nb067AlphaDummy049), (nb067AlphaDummy050 x y)),
        ((nb067AlphaDummy047), (nb067AlphaDummy048 x y)),
        ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
        ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
        ((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
        ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy029))
            (synCun (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy032 x y))
            (synCun (Class.cv (nb067AlphaDummy033 x y))
              (Class.cv (nb067AlphaDummy034 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy031), (nb067AlphaDummy034 x y)),
          ((nb067AlphaDummy030), (nb067AlphaDummy033 x y)),
          ((nb067AlphaDummy029), (nb067AlphaDummy032 x y)),
          ((nb067AlphaDummy027), (nb067AlphaDummy028 x y)),
          ((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
          ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
          ((nb067AlphaDummy049), (nb067AlphaDummy050 x y)),
          ((nb067AlphaDummy047), (nb067AlphaDummy048 x y)),
          ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
          ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
          ((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
          ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
          ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
          ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
          ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
          ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part011`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0003`. -/
@[expose]
noncomputable def nb067SplitAlpha0003 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
        ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
        ((nb067AlphaDummy049), (nb067AlphaDummy050 x y)),
        ((nb067AlphaDummy047), (nb067AlphaDummy048 x y)),
        ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
        ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
        ((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
        ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy023))
          (Class.cv (nb067AlphaDummy016))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy024))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy023)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy023)) (synC1c))
              (Class.cv (nb067AlphaDummy023))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy025 x y))
          (Class.cv (nb067AlphaDummy018 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy026 x y))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy025 x y)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy025 x y)) (synC1c))
              (Class.cv (nb067AlphaDummy025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0058) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0059 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0056) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0057 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy016))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy018 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0024) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0025 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0024) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0025 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0022) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy031), (nb067AlphaDummy034 x y)),
                                  ((nb067AlphaDummy030), (nb067AlphaDummy033 x y)),
                                  ((nb067AlphaDummy029), (nb067AlphaDummy032 x y)),
                                  ((nb067AlphaDummy027), (nb067AlphaDummy028 x y)),
                                  ((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
                                  ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
                                  ((nb067AlphaDummy049), (nb067AlphaDummy050 x y)),
                                  ((nb067AlphaDummy047), (nb067AlphaDummy048 x y)),
                                  ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
                                  ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
                                  ((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
                                  ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
                                  ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                                  ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                                  ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                                  ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0002 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy027), (nb067AlphaDummy028 x y)),
                      ((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
                      ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
                      ((nb067AlphaDummy049), (nb067AlphaDummy050 x y)),
                      ((nb067AlphaDummy047), (nb067AlphaDummy048 x y)),
                      ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
                      ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
                      ((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
                      ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
                      ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                      ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                      ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                      ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy027), (nb067AlphaDummy028 x y)),
                      ((nb067AlphaDummy023), (nb067AlphaDummy025 x y)),
                      ((nb067AlphaDummy024), (nb067AlphaDummy026 x y)),
                      ((nb067AlphaDummy049), (nb067AlphaDummy050 x y)),
                      ((nb067AlphaDummy047), (nb067AlphaDummy048 x y)),
                      ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
                      ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
                      ((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
                      ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
                      ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                      ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                      ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                      ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as
`nb067_second_coordinate_occurrence`.
-/
@[expose]
noncomputable def nb067SecondCoordinateOccurrence (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [(nb067AlphaDummy016, (nb067AlphaDummy018 x y)),
        (nb067AlphaDummy015, (nb067AlphaDummy017 x y)),
        ((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
        ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Class.cv (nb067AlphaDummy002)) (Class.cv y) :=
  by
  have freshness0 : (nb067AlphaDummy002) ≠ nb067AlphaDummy016 :=
    by
    unfold nb067AlphaDummy016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 1))
  have freshness1 : y ≠ (nb067AlphaDummy018 x y) :=
    by
    unfold nb067AlphaDummy018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 1))
  have freshness2 : (nb067AlphaDummy002) ≠ nb067AlphaDummy015 :=
    by
    unfold nb067AlphaDummy015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 0))
  have freshness3 : y ≠ (nb067AlphaDummy017 x y) :=
    by
    unfold nb067AlphaDummy017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 0))
  have freshness4 : (nb067AlphaDummy002) ≠ (nb067AlphaDummy045) :=
    by
    unfold nb067AlphaDummy045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0054) 0))
  have freshness5 : y ≠ (nb067AlphaDummy046 x y) :=
    by
    unfold nb067AlphaDummy046
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0055 x y) 0))
  have freshness6 : (nb067AlphaDummy002) ≠ (nb067AlphaDummy019) :=
    by
    unfold nb067AlphaDummy019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0051) 0))
  have freshness7 : y ≠ (nb067AlphaDummy020 x y) :=
    by
    unfold nb067AlphaDummy020
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0053 x y) 0))
  have freshness8 : (nb067AlphaDummy002) ≠ (nb067AlphaDummy008) :=
    by
    unfold nb067AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 1))
  have freshness9 : y ≠ (nb067AlphaDummy010 x y f) :=
    by
    unfold nb067AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 1))
  have freshness10 : (nb067AlphaDummy002) ≠ (nb067AlphaDummy007) :=
    by
    unfold nb067AlphaDummy007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 0))
  have freshness11 : y ≠ (nb067AlphaDummy009 x y f) :=
    by
    unfold nb067AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 0))
  have freshness12 : (nb067AlphaDummy002) ≠ (nb067AlphaDummy013) :=
    by
    unfold nb067AlphaDummy013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0048) 0))
  have freshness13 : y ≠ (nb067AlphaDummy014 x y f) :=
    by
    unfold nb067AlphaDummy014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0049 x y f) 0))
  have freshness14 : (nb067AlphaDummy002) ≠ (nb067AlphaDummy011) :=
    by
    unfold nb067AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0045) 0))
  have freshness15 : y ≠ (nb067AlphaDummy012 x y f) :=
    by
    unfold nb067AlphaDummy012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0047 x y f) 0))
  have freshness16 : (nb067AlphaDummy002) ≠ (nb067AlphaDummy003) :=
    by
    unfold nb067AlphaDummy003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0042) 0))
  have freshness17 : y ≠ (nb067AlphaDummy004 x y f) :=
    by
    unfold nb067AlphaDummy004
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0043 x y f) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13
                      (TAlphaVar.there freshness14 freshness15
                        (TAlphaVar.there freshness16 freshness17
                          (TAlphaVar.here _ _ _)))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0004`. -/
@[expose]
noncomputable def nb067SplitAlpha0004 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
        ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy045))
          (Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCun (synCphi (Class.cv (nb067AlphaDummy016))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy045))
            (Class.cab (nb067AlphaDummy015)
              (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
                (Wff.classEq (Class.cv (nb067AlphaDummy015))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy046 x y))
          (Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy046 x y))
            (Class.cab (nb067AlphaDummy017 x y)
              (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (nb067SecondCoordinateOccurrence x y f)) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy001))).fv ∪
                      ((Class.cv (nb067AlphaDummy002))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0003 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0003 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy047), (nb067AlphaDummy048 x y)),
                          ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
                          ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
                          ((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
                          ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
                          ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                          ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                          ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                          ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (nb067SecondCoordinateOccurrence x y f)) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy001))).fv ∪
                        ((Class.cv (nb067AlphaDummy002))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0003 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0003 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy047), (nb067AlphaDummy048 x y)),
                            ((nb067AlphaDummy016), (nb067AlphaDummy018 x y)),
                            ((nb067AlphaDummy015), (nb067AlphaDummy017 x y)),
                            ((nb067AlphaDummy045), (nb067AlphaDummy046 x y)),
                            ((nb067AlphaDummy019), (nb067AlphaDummy020 x y)),
                            ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                            ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                            ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                            ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0005`. -/
@[expose]
noncomputable def nb067SplitAlpha0005 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy059), (nb067AlphaDummy062 x y f)),
        ((nb067AlphaDummy058), (nb067AlphaDummy061 x y f)),
        ((nb067AlphaDummy057), (nb067AlphaDummy060 x y f)),
        ((nb067AlphaDummy055), (nb067AlphaDummy056 x y f)),
        ((nb067AlphaDummy051), (nb067AlphaDummy053 x y f)),
        ((nb067AlphaDummy052), (nb067AlphaDummy054 x y f)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy057))
            (synCun (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy060 x y f))
            (synCun (Class.cv (nb067AlphaDummy061 x y f))
              (Class.cv (nb067AlphaDummy062 x y f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy059), (nb067AlphaDummy062 x y f)),
          ((nb067AlphaDummy058), (nb067AlphaDummy061 x y f)),
          ((nb067AlphaDummy057), (nb067AlphaDummy060 x y f)),
          ((nb067AlphaDummy055), (nb067AlphaDummy056 x y f)),
          ((nb067AlphaDummy051), (nb067AlphaDummy053 x y f)),
          ((nb067AlphaDummy052), (nb067AlphaDummy054 x y f)),
          ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
          ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
          ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
          ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪
                                    ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪
                                    ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as
`nb067_first_coordinate_occurrence`.
-/
@[expose]
noncomputable def nb067FirstCoordinateOccurrence (x : Var) (y : Var) (f : Var)
    (dv_x_y : x ≠ y) :
    TAlphaClass
      [(nb067AlphaDummy016, (nb067AlphaDummy018 x y)),
        (nb067AlphaDummy015, (nb067AlphaDummy017 x y)),
        (nb067AlphaDummy021, (nb067AlphaDummy022 x y)),
        (nb067AlphaDummy019, (nb067AlphaDummy020 x y)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Class.cv (nb067AlphaDummy001)) (Class.cv x) :=
  by
  have freshness0 : (nb067AlphaDummy001) ≠ nb067AlphaDummy016 :=
    by
    unfold nb067AlphaDummy016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 1))
  have freshness1 : x ≠ (nb067AlphaDummy018 x y) :=
    by
    unfold nb067AlphaDummy018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 1))
  have freshness2 : (nb067AlphaDummy001) ≠ nb067AlphaDummy015 :=
    by
    unfold nb067AlphaDummy015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 0))
  have freshness3 : x ≠ (nb067AlphaDummy017 x y) :=
    by
    unfold nb067AlphaDummy017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 0))
  have freshness4 : (nb067AlphaDummy001) ≠ nb067AlphaDummy021 :=
    by
    unfold nb067AlphaDummy021
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0018) 0))
  have freshness5 : x ≠ (nb067AlphaDummy022 x y) :=
    by
    unfold nb067AlphaDummy022
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0019 x y) 0))
  have freshness6 : (nb067AlphaDummy001) ≠ nb067AlphaDummy019 :=
    by
    unfold nb067AlphaDummy019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0015) 0))
  have freshness7 : x ≠ (nb067AlphaDummy020 x y) :=
    by
    unfold nb067AlphaDummy020
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0017 x y) 0))
  have freshness8 : (nb067AlphaDummy001) ≠ (nb067AlphaDummy008) :=
    by
    unfold nb067AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 1))
  have freshness9 : x ≠ (nb067AlphaDummy010 x y f) :=
    by
    unfold nb067AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 1))
  have freshness10 : (nb067AlphaDummy001) ≠ (nb067AlphaDummy007) :=
    by
    unfold nb067AlphaDummy007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 0))
  have freshness11 : x ≠ (nb067AlphaDummy009 x y f) :=
    by
    unfold nb067AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 0))
  have freshness12 : (nb067AlphaDummy001) ≠ (nb067AlphaDummy013) :=
    by
    unfold nb067AlphaDummy013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0012) 0))
  have freshness13 : x ≠ (nb067AlphaDummy014 x y f) :=
    by
    unfold nb067AlphaDummy014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0013 x y f) 0))
  have freshness14 : (nb067AlphaDummy001) ≠ (nb067AlphaDummy011) :=
    by
    unfold nb067AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0009) 0))
  have freshness15 : x ≠ (nb067AlphaDummy012 x y f) :=
    by
    unfold nb067AlphaDummy012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0011 x y f) 0))
  have freshness16 : (nb067AlphaDummy001) ≠ (nb067AlphaDummy003) :=
    by
    unfold nb067AlphaDummy003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0006) 0))
  have freshness17 : x ≠ (nb067AlphaDummy004 x y f) :=
    by
    unfold nb067AlphaDummy004
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0007 x y f) 0))
  have freshness18 : (nb067AlphaDummy001) ≠ (nb067AlphaDummy002) :=
    by
    unfold nb067AlphaDummy001 nb067AlphaDummy002
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness19 : x ≠ y := by exact dv_x_y
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13
                      (TAlphaVar.there freshness14 freshness15
                        (TAlphaVar.there freshness16 freshness17
                          (TAlphaVar.there freshness18 freshness19
                            (TAlphaVar.here _ _ _))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0006`. -/
@[expose]
noncomputable def nb067SplitAlpha0006 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy008))
          (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002))))
        (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy007))
            (synCphi (Class.cv (nb067AlphaDummy008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy010 x y f))
          (synCop (Class.cv x) (Class.cv y))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
            (synCphi (Class.cv (nb067AlphaDummy010 x y f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb067FirstCoordinateOccurrence x y f dv_x_y))
                            (nb067SplitAlpha0001 x y f)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb067FirstCoordinateOccurrence x y f dv_x_y))
                            (nb067SplitAlpha0001 x y f)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0004 x y f)))))))))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((synCop (Class.cv (nb067AlphaDummy001))
                    (Class.cv (nb067AlphaDummy002)))).fv ∪
                ((Class.cv (nb067AlphaDummy003))).fv) (by decide)) (freshVar_injective
              (((synCop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb067AlphaDummy004 x y f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy010 x y f))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0064) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0065 x y f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0064) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0065 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0063 x y f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb067AlphaDummy059),
        (nb067AlphaDummy062 x y f)), ((nb067AlphaDummy058),
        (nb067AlphaDummy061 x y f)), ((nb067AlphaDummy057),
        (nb067AlphaDummy060 x y f)), ((nb067AlphaDummy055),
        (nb067AlphaDummy056 x y f)), ((nb067AlphaDummy051),
        (nb067AlphaDummy053 x y f)), ((nb067AlphaDummy052),
        (nb067AlphaDummy054 x y f)), ((nb067AlphaDummy008),
        (nb067AlphaDummy010 x y f)), ((nb067AlphaDummy007),
        (nb067AlphaDummy009 x y f)), ((nb067AlphaDummy013),
        (nb067AlphaDummy014 x y f)), ((nb067AlphaDummy011),
        (nb067AlphaDummy012 x y f)), ((nb067AlphaDummy003),
        (nb067AlphaDummy004 x y f)), ((nb067AlphaDummy002), y),
        ((nb067AlphaDummy001), x), ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb067SplitAlpha0005 x y f))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb067AlphaDummy055), (nb067AlphaDummy056 x y f)),
                              ((nb067AlphaDummy051), (nb067AlphaDummy053 x y f)),
                              ((nb067AlphaDummy052), (nb067AlphaDummy054 x y f)),
                              ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                              ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                              ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                              ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb067AlphaDummy055), (nb067AlphaDummy056 x y f)),
                              ((nb067AlphaDummy051), (nb067AlphaDummy053 x y f)),
                              ((nb067AlphaDummy052), (nb067AlphaDummy054 x y f)),
                              ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                              ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                              ((nb067AlphaDummy013), (nb067AlphaDummy014 x y f)),
                              ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part012`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0007`. -/
@[expose]
noncomputable def nb067SplitAlpha0007 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy059), (nb067AlphaDummy062 x y f)),
        ((nb067AlphaDummy058), (nb067AlphaDummy061 x y f)),
        ((nb067AlphaDummy057), (nb067AlphaDummy060 x y f)),
        ((nb067AlphaDummy055), (nb067AlphaDummy056 x y f)),
        ((nb067AlphaDummy051), (nb067AlphaDummy053 x y f)),
        ((nb067AlphaDummy052), (nb067AlphaDummy054 x y f)),
        ((nb067AlphaDummy077), (nb067AlphaDummy078 x y f)),
        ((nb067AlphaDummy075), (nb067AlphaDummy076 x y f)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy073), (nb067AlphaDummy074 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy057))
            (synCun (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy060 x y f))
            (synCun (Class.cv (nb067AlphaDummy061 x y f))
              (Class.cv (nb067AlphaDummy062 x y f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy059), (nb067AlphaDummy062 x y f)),
          ((nb067AlphaDummy058), (nb067AlphaDummy061 x y f)),
          ((nb067AlphaDummy057), (nb067AlphaDummy060 x y f)),
          ((nb067AlphaDummy055), (nb067AlphaDummy056 x y f)),
          ((nb067AlphaDummy051), (nb067AlphaDummy053 x y f)),
          ((nb067AlphaDummy052), (nb067AlphaDummy054 x y f)),
          ((nb067AlphaDummy077), (nb067AlphaDummy078 x y f)),
          ((nb067AlphaDummy075), (nb067AlphaDummy076 x y f)),
          ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
          ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
          ((nb067AlphaDummy073), (nb067AlphaDummy074 x y f)),
          ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪
                                    ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪
                                    ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0008`. -/
@[expose]
noncomputable def nb067SplitAlpha0008 (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [((nb067AlphaDummy077), (nb067AlphaDummy078 x y f)),
        ((nb067AlphaDummy075), (nb067AlphaDummy076 x y f)),
        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
        ((nb067AlphaDummy073), (nb067AlphaDummy074 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Class.cab (nb067AlphaDummy052)
        (synWrex (nb067AlphaDummy051) (Class.cv (nb067AlphaDummy008))
          (Wff.classEq (Class.cv (nb067AlphaDummy052))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy051)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy051)) (synC1c))
              (Class.cv (nb067AlphaDummy051))))))
      (Class.cab (nb067AlphaDummy054 x y f)
        (synWrex (nb067AlphaDummy053 x y f) (Class.cv (nb067AlphaDummy010 x y f))
          (Wff.classEq (Class.cv (nb067AlphaDummy054 x y f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy053 x y f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy053 x y f)) (synC1c))
              (Class.cv (nb067AlphaDummy053 x y f)))))) :=
  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0090) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0091 x y f) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0088) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0089 x y f) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (nb067AlphaDummy008))).fv) (by decide))
              (freshVar_injective (((Class.cv (nb067AlphaDummy010 x y f))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0064) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0065 x y f) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0064) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0065 x y f) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0062) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed [((nb067AlphaDummy059),
                                      (nb067AlphaDummy062 x y f)), ((nb067AlphaDummy058),
                                      (nb067AlphaDummy061 x y f)), ((nb067AlphaDummy057),
                                      (nb067AlphaDummy060 x y f)), ((nb067AlphaDummy055),
                                      (nb067AlphaDummy056 x y f)), ((nb067AlphaDummy051),
                                      (nb067AlphaDummy053 x y f)), ((nb067AlphaDummy052),
                                      (nb067AlphaDummy054 x y f)), ((nb067AlphaDummy077),
                                      (nb067AlphaDummy078 x y f)), ((nb067AlphaDummy075),
                                      (nb067AlphaDummy076 x y f)), ((nb067AlphaDummy008),
                                      (nb067AlphaDummy010 x y f)), ((nb067AlphaDummy007),
                                      (nb067AlphaDummy009 x y f)), ((nb067AlphaDummy073),
                                      (nb067AlphaDummy074 x y f)), ((nb067AlphaDummy011),
                                      (nb067AlphaDummy012 x y f)), ((nb067AlphaDummy003),
                                      (nb067AlphaDummy004 x y f)),
                                    ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                    ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                  (synC1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb067SplitAlpha0007 x y f))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((nb067AlphaDummy055), (nb067AlphaDummy056 x y f)),
                        ((nb067AlphaDummy051), (nb067AlphaDummy053 x y f)),
                        ((nb067AlphaDummy052), (nb067AlphaDummy054 x y f)),
                        ((nb067AlphaDummy077), (nb067AlphaDummy078 x y f)),
                        ((nb067AlphaDummy075), (nb067AlphaDummy076 x y f)),
                        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                        ((nb067AlphaDummy073), (nb067AlphaDummy074 x y f)),
                        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                      (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((nb067AlphaDummy055), (nb067AlphaDummy056 x y f)),
                        ((nb067AlphaDummy051), (nb067AlphaDummy053 x y f)),
                        ((nb067AlphaDummy052), (nb067AlphaDummy054 x y f)),
                        ((nb067AlphaDummy077), (nb067AlphaDummy078 x y f)),
                        ((nb067AlphaDummy075), (nb067AlphaDummy076 x y f)),
                        ((nb067AlphaDummy008), (nb067AlphaDummy010 x y f)),
                        ((nb067AlphaDummy007), (nb067AlphaDummy009 x y f)),
                        ((nb067AlphaDummy073), (nb067AlphaDummy074 x y f)),
                        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
                        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                      (synCnnc) (by simp only [fv_syn_cnnc])))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_function_graph_occurrence`. -/
@[expose]
noncomputable def nb067FunctionGraphOccurrence (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [(nb067AlphaDummy008, (nb067AlphaDummy010 x y f)),
        (nb067AlphaDummy007, (nb067AlphaDummy009 x y f)),
        (nb067AlphaDummy073, (nb067AlphaDummy074 x y f)),
        ((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Class.cv (nb067AlphaDummy003)) (Class.cv (nb067AlphaDummy004 x y f)) :=
  by
  have freshness0 : (nb067AlphaDummy003) ≠ nb067AlphaDummy008 :=
    by
    unfold nb067AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1))
  have freshness1 : (nb067AlphaDummy004 x y f) ≠ (nb067AlphaDummy010 x y f) :=
    by
    unfold nb067AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1))
  have freshness2 : (nb067AlphaDummy003) ≠ nb067AlphaDummy007 :=
    by
    unfold nb067AlphaDummy007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0))
  have freshness3 : (nb067AlphaDummy004 x y f) ≠ (nb067AlphaDummy009 x y f) :=
    by
    unfold nb067AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0))
  have freshness4 : (nb067AlphaDummy003) ≠ nb067AlphaDummy073 :=
    by
    unfold nb067AlphaDummy073
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0086) 0))
  have freshness5 : (nb067AlphaDummy004 x y f) ≠ (nb067AlphaDummy074 x y f) :=
    by
    unfold nb067AlphaDummy074
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0087 x y f) 0))
  have freshness6 : (nb067AlphaDummy003) ≠ (nb067AlphaDummy011) :=
    by
    unfold nb067AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0083) 0))
  have freshness7 : (nb067AlphaDummy004 x y f) ≠ (nb067AlphaDummy012 x y f) :=
    by
    unfold nb067AlphaDummy012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0085 x y f) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.here _ _ _))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0009`. -/
@[expose]
noncomputable def nb067SplitAlpha0009 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb067AlphaDummy011), (nb067AlphaDummy012 x y f)),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy011)) (synCcompl
            (Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
                (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCphi (Class.cv (nb067AlphaDummy008)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy011)) (synCcompl
              (Class.cab (nb067AlphaDummy007)
                (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
                  (Wff.classEq (Class.cv (nb067AlphaDummy007))
                    (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy012 x y f)) (synCcompl
            (Class.cab (nb067AlphaDummy009 x y f)
              (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCphi (Class.cv (nb067AlphaDummy010 x y f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy012 x y f)) (synCcompl
              (Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
                  (Class.cv (nb067AlphaDummy004 x y f))
                  (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                    (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb067SplitAlpha0006 x y f dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb067SplitAlpha0006 x y f dv_x_y)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb067FunctionGraphOccurrence x y f)) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((synCop (Class.cv (nb067AlphaDummy001))
                                    (Class.cv (nb067AlphaDummy002)))).fv ∪
                                ((Class.cv (nb067AlphaDummy003))).fv) (by decide))
                            (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb067AlphaDummy004 x y f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb067SplitAlpha0008 x y f)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb067SplitAlpha0008 x y f))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed [((nb067AlphaDummy075),
                                      (nb067AlphaDummy076 x y f)), ((nb067AlphaDummy008),
                                      (nb067AlphaDummy010 x y f)), ((nb067AlphaDummy007),
                                      (nb067AlphaDummy009 x y f)), ((nb067AlphaDummy073),
                                      (nb067AlphaDummy074 x y f)), ((nb067AlphaDummy011),
                                      (nb067AlphaDummy012 x y f)), ((nb067AlphaDummy003),
                                      (nb067AlphaDummy004 x y f)),
                                    ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                    ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb067FunctionGraphOccurrence x y f)) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((synCop (Class.cv (nb067AlphaDummy001))
                                    (Class.cv (nb067AlphaDummy002)))).fv ∪
                                ((Class.cv (nb067AlphaDummy003))).fv) (by decide))
                            (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb067AlphaDummy004 x y f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb067SplitAlpha0008 x y f)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb067SplitAlpha0008 x y f))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed [((nb067AlphaDummy075),
                                      (nb067AlphaDummy076 x y f)), ((nb067AlphaDummy008),
                                      (nb067AlphaDummy010 x y f)), ((nb067AlphaDummy007),
                                      (nb067AlphaDummy009 x y f)), ((nb067AlphaDummy073),
                                      (nb067AlphaDummy074 x y f)), ((nb067AlphaDummy011),
                                      (nb067AlphaDummy012 x y f)), ((nb067AlphaDummy003),
                                      (nb067AlphaDummy004 x y f)),
                                    ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                    ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

theorem nb067_compact_fv_empty_0086 : (nb067AlphaDummy081) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0087 (f : Var) :
    (nb067AlphaDummy082 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0088 : (nb067AlphaDummy079) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0089 (f : Var) :
    (nb067AlphaDummy080 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0090 : (nb067AlphaDummy000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0091 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
