/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C055C001Part005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C055C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0000`. -/
@[expose]
noncomputable def nb055SplitAlpha0000 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy030), (nb055AlphaDummy033 x y)),
        ((nb055AlphaDummy029), (nb055AlphaDummy032 x y)),
        ((nb055AlphaDummy028), (nb055AlphaDummy031 x y)),
        ((nb055AlphaDummy026), (nb055AlphaDummy027 x y)),
        ((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
        ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy020), (nb055AlphaDummy021 x y)),
        ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy028))
            (synCun (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy031 x y))
            (synCun (Class.cv (nb055AlphaDummy032 x y))
              (Class.cv (nb055AlphaDummy033 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy030), (nb055AlphaDummy033 x y)),
          ((nb055AlphaDummy029), (nb055AlphaDummy032 x y)),
          ((nb055AlphaDummy028), (nb055AlphaDummy031 x y)),
          ((nb055AlphaDummy026), (nb055AlphaDummy027 x y)),
          ((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
          ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
          ((nb055AlphaDummy020), (nb055AlphaDummy021 x y)),
          ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
          ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
          ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
          ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
          ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0001`. -/
@[expose]
noncomputable def nb055SplitAlpha0001 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy020), (nb055AlphaDummy021 x y)),
        ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.classEq (Class.cv (nb055AlphaDummy014))
        (synCphi (Class.cv (nb055AlphaDummy015))))
      (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
        (synCphi (Class.cv (nb055AlphaDummy017 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv)
          (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb055AlphaDummy015))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb055AlphaDummy017 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0024) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0025 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0024) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0025 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0022) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed [((nb055AlphaDummy030),
                                        (nb055AlphaDummy033 x y)), ((nb055AlphaDummy029),
                                        (nb055AlphaDummy032 x y)), ((nb055AlphaDummy028),
                                        (nb055AlphaDummy031 x y)), ((nb055AlphaDummy026),
                                        (nb055AlphaDummy027 x y)), ((nb055AlphaDummy022),
                                        (nb055AlphaDummy024 x y)), ((nb055AlphaDummy023),
                                        (nb055AlphaDummy025 x y)), ((nb055AlphaDummy015),
                                        (nb055AlphaDummy017 x y)), ((nb055AlphaDummy014),
                                        (nb055AlphaDummy016 x y)), ((nb055AlphaDummy020),
                                        (nb055AlphaDummy021 x y)), ((nb055AlphaDummy018),
                                        (nb055AlphaDummy019 x y)), ((nb055AlphaDummy007),
                                        (nb055AlphaDummy009 x y)), ((nb055AlphaDummy006),
                                        (nb055AlphaDummy008 x y)), ((nb055AlphaDummy012),
                                        (nb055AlphaDummy013 x y)), ((nb055AlphaDummy010),
                                        (nb055AlphaDummy011 x y)), ((nb055AlphaDummy002),
                                        (nb055AlphaDummy003 x y)),
                                      ((nb055AlphaDummy001), y),
                                      ((nb055AlphaDummy000), x), ((nb055AlphaDummy004),
                                        (nb055AlphaDummy005 x y))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb055SplitAlpha0000 x y))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy026), (nb055AlphaDummy027 x y)),
                          ((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
                          ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy020), (nb055AlphaDummy021 x y)),
                          ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
                          ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                          ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                          ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
                          ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy026), (nb055AlphaDummy027 x y)),
                          ((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
                          ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy020), (nb055AlphaDummy021 x y)),
                          ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
                          ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                          ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                          ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
                          ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0002`. -/
@[expose]
noncomputable def nb055SplitAlpha0002 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy030), (nb055AlphaDummy033 x y)),
        ((nb055AlphaDummy029), (nb055AlphaDummy032 x y)),
        ((nb055AlphaDummy028), (nb055AlphaDummy031 x y)),
        ((nb055AlphaDummy026), (nb055AlphaDummy027 x y)),
        ((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
        ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
        ((nb055AlphaDummy048), (nb055AlphaDummy049 x y)),
        ((nb055AlphaDummy046), (nb055AlphaDummy047 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy044), (nb055AlphaDummy045 x y)),
        ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy028))
            (synCun (Class.cv (nb055AlphaDummy029)) (Class.cv (nb055AlphaDummy030))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy032 x y))
            (Class.cv (nb055AlphaDummy033 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy031 x y))
            (synCun (Class.cv (nb055AlphaDummy032 x y))
              (Class.cv (nb055AlphaDummy033 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy030), (nb055AlphaDummy033 x y)),
          ((nb055AlphaDummy029), (nb055AlphaDummy032 x y)),
          ((nb055AlphaDummy028), (nb055AlphaDummy031 x y)),
          ((nb055AlphaDummy026), (nb055AlphaDummy027 x y)),
          ((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
          ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
          ((nb055AlphaDummy048), (nb055AlphaDummy049 x y)),
          ((nb055AlphaDummy046), (nb055AlphaDummy047 x y)),
          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
          ((nb055AlphaDummy044), (nb055AlphaDummy045 x y)),
          ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
          ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
          ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
          ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
          ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy022))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy024 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part007`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0003`. -/
@[expose]
noncomputable def nb055SplitAlpha0003 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
        ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
        ((nb055AlphaDummy048), (nb055AlphaDummy049 x y)),
        ((nb055AlphaDummy046), (nb055AlphaDummy047 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy044), (nb055AlphaDummy045 x y)),
        ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy022))
          (Class.cv (nb055AlphaDummy015))) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy023))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy022)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy022)) (synC1c))
              (Class.cv (nb055AlphaDummy022))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy024 x y))
          (Class.cv (nb055AlphaDummy017 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy025 x y))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy024 x y)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy024 x y)) (synC1c))
              (Class.cv (nb055AlphaDummy024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0058) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0059 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0056) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0057 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy015))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb055AlphaDummy017 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0024) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0025 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0024) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0025 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0022) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb055AlphaDummy030), (nb055AlphaDummy033 x y)),
                                  ((nb055AlphaDummy029), (nb055AlphaDummy032 x y)),
                                  ((nb055AlphaDummy028), (nb055AlphaDummy031 x y)),
                                  ((nb055AlphaDummy026), (nb055AlphaDummy027 x y)),
                                  ((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
                                  ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
                                  ((nb055AlphaDummy048), (nb055AlphaDummy049 x y)),
                                  ((nb055AlphaDummy046), (nb055AlphaDummy047 x y)),
                                  ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                                  ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                                  ((nb055AlphaDummy044), (nb055AlphaDummy045 x y)),
                                  ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
                                  ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                                  ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                                  ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
                                  ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                                  ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                                  ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                                  ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb055SplitAlpha0002 x y))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb055AlphaDummy026), (nb055AlphaDummy027 x y)),
                      ((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
                      ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
                      ((nb055AlphaDummy048), (nb055AlphaDummy049 x y)),
                      ((nb055AlphaDummy046), (nb055AlphaDummy047 x y)),
                      ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                      ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                      ((nb055AlphaDummy044), (nb055AlphaDummy045 x y)),
                      ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
                      ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                      ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                      ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
                      ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                      ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                      ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                      ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb055AlphaDummy026), (nb055AlphaDummy027 x y)),
                      ((nb055AlphaDummy022), (nb055AlphaDummy024 x y)),
                      ((nb055AlphaDummy023), (nb055AlphaDummy025 x y)),
                      ((nb055AlphaDummy048), (nb055AlphaDummy049 x y)),
                      ((nb055AlphaDummy046), (nb055AlphaDummy047 x y)),
                      ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                      ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                      ((nb055AlphaDummy044), (nb055AlphaDummy045 x y)),
                      ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
                      ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                      ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                      ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
                      ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                      ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                      ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                      ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_variable_occurrence_0`. -/
@[expose]
noncomputable def nb055VariableOccurrence0 (x y : Var) :
    TAlphaClass
      [(nb055AlphaDummy015, (nb055AlphaDummy017 x y)),
        (nb055AlphaDummy014, (nb055AlphaDummy016 x y)),
        (nb055AlphaDummy044, (nb055AlphaDummy045 x y)),
        (nb055AlphaDummy018, (nb055AlphaDummy019 x y)),
        (nb055AlphaDummy007, (nb055AlphaDummy009 x y)),
        (nb055AlphaDummy006, (nb055AlphaDummy008 x y)),
        (nb055AlphaDummy012, (nb055AlphaDummy013 x y)),
        (nb055AlphaDummy010, (nb055AlphaDummy011 x y)),
        (nb055AlphaDummy002, (nb055AlphaDummy003 x y)), (nb055AlphaDummy001, y),
        (nb055AlphaDummy000, x), (nb055AlphaDummy004, (nb055AlphaDummy005 x y))]
      (Class.cv nb055AlphaDummy001) (Class.cv y) :=
  by
  have freshness0 : nb055AlphaDummy001 ≠ nb055AlphaDummy015 :=
    by
    unfold nb055AlphaDummy015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
  have freshness1 : y ≠ (nb055AlphaDummy017 x y) :=
    by
    unfold nb055AlphaDummy017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
  have freshness2 : nb055AlphaDummy001 ≠ nb055AlphaDummy014 :=
    by
    unfold nb055AlphaDummy014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  have freshness3 : y ≠ (nb055AlphaDummy016 x y) :=
    by
    unfold nb055AlphaDummy016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  have freshness4 : nb055AlphaDummy001 ≠ nb055AlphaDummy044 :=
    by
    unfold nb055AlphaDummy044
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0054) 0))
  have freshness5 : y ≠ (nb055AlphaDummy045 x y) :=
    by
    unfold nb055AlphaDummy045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0055 x y) 0))
  have freshness6 : nb055AlphaDummy001 ≠ nb055AlphaDummy018 :=
    by
    unfold nb055AlphaDummy018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0051) 0))
  have freshness7 : y ≠ (nb055AlphaDummy019 x y) :=
    by
    unfold nb055AlphaDummy019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0053 x y) 0))
  have freshness8 : nb055AlphaDummy001 ≠ nb055AlphaDummy007 :=
    by
    unfold nb055AlphaDummy007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1))
  have freshness9 : y ≠ (nb055AlphaDummy009 x y) :=
    by
    unfold nb055AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1))
  have freshness10 : nb055AlphaDummy001 ≠ nb055AlphaDummy006 :=
    by
    unfold nb055AlphaDummy006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0))
  have freshness11 : y ≠ (nb055AlphaDummy008 x y) :=
    by
    unfold nb055AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0))
  have freshness12 : nb055AlphaDummy001 ≠ nb055AlphaDummy012 :=
    by
    unfold nb055AlphaDummy012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0048) 0))
  have freshness13 : y ≠ (nb055AlphaDummy013 x y) :=
    by
    unfold nb055AlphaDummy013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0049 x y) 0))
  have freshness14 : nb055AlphaDummy001 ≠ nb055AlphaDummy010 :=
    by
    unfold nb055AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0045) 0))
  have freshness15 : y ≠ (nb055AlphaDummy011 x y) :=
    by
    unfold nb055AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0047 x y) 0))
  have freshness16 : nb055AlphaDummy001 ≠ nb055AlphaDummy002 :=
    by
    unfold nb055AlphaDummy002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0042) 0))
  have freshness17 : y ≠ (nb055AlphaDummy003 x y) :=
    by
    unfold nb055AlphaDummy003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0043 x y) 0))
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


/-- Checked nominal proof certificate identified upstream as `nb055_variable_occurrence_1`. -/
@[expose]
noncomputable def nb055_variable_occurrence_1 (x y : Var) (dv_x_y : x ≠ y) :
    TAlphaClass
      [(nb055AlphaDummy015, (nb055AlphaDummy017 x y)),
        (nb055AlphaDummy014, (nb055AlphaDummy016 x y)),
        (nb055AlphaDummy020, (nb055AlphaDummy021 x y)),
        (nb055AlphaDummy018, (nb055AlphaDummy019 x y)),
        (nb055AlphaDummy007, (nb055AlphaDummy009 x y)),
        (nb055AlphaDummy006, (nb055AlphaDummy008 x y)),
        (nb055AlphaDummy012, (nb055AlphaDummy013 x y)),
        (nb055AlphaDummy010, (nb055AlphaDummy011 x y)),
        (nb055AlphaDummy002, (nb055AlphaDummy003 x y)), (nb055AlphaDummy001, y),
        (nb055AlphaDummy000, x), (nb055AlphaDummy004, (nb055AlphaDummy005 x y))]
      (Class.cv nb055AlphaDummy000) (Class.cv x) :=
  by
  have freshness0 : nb055AlphaDummy000 ≠ nb055AlphaDummy015 :=
    by
    unfold nb055AlphaDummy015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
  have freshness1 : x ≠ (nb055AlphaDummy017 x y) :=
    by
    unfold nb055AlphaDummy017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
  have freshness2 : nb055AlphaDummy000 ≠ nb055AlphaDummy014 :=
    by
    unfold nb055AlphaDummy014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  have freshness3 : x ≠ (nb055AlphaDummy016 x y) :=
    by
    unfold nb055AlphaDummy016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  have freshness4 : nb055AlphaDummy000 ≠ nb055AlphaDummy020 :=
    by
    unfold nb055AlphaDummy020
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0018) 0))
  have freshness5 : x ≠ (nb055AlphaDummy021 x y) :=
    by
    unfold nb055AlphaDummy021
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0019 x y) 0))
  have freshness6 : nb055AlphaDummy000 ≠ nb055AlphaDummy018 :=
    by
    unfold nb055AlphaDummy018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0015) 0))
  have freshness7 : x ≠ (nb055AlphaDummy019 x y) :=
    by
    unfold nb055AlphaDummy019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0017 x y) 0))
  have freshness8 : nb055AlphaDummy000 ≠ nb055AlphaDummy007 :=
    by
    unfold nb055AlphaDummy007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1))
  have freshness9 : x ≠ (nb055AlphaDummy009 x y) :=
    by
    unfold nb055AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1))
  have freshness10 : nb055AlphaDummy000 ≠ nb055AlphaDummy006 :=
    by
    unfold nb055AlphaDummy006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0))
  have freshness11 : x ≠ (nb055AlphaDummy008 x y) :=
    by
    unfold nb055AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0))
  have freshness12 : nb055AlphaDummy000 ≠ nb055AlphaDummy012 :=
    by
    unfold nb055AlphaDummy012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0012) 0))
  have freshness13 : x ≠ (nb055AlphaDummy013 x y) :=
    by
    unfold nb055AlphaDummy013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0013 x y) 0))
  have freshness14 : nb055AlphaDummy000 ≠ nb055AlphaDummy010 :=
    by
    unfold nb055AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0009) 0))
  have freshness15 : x ≠ (nb055AlphaDummy011 x y) :=
    by
    unfold nb055AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0011 x y) 0))
  have freshness16 : nb055AlphaDummy000 ≠ nb055AlphaDummy002 :=
    by
    unfold nb055AlphaDummy002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0006) 0))
  have freshness17 : x ≠ (nb055AlphaDummy003 x y) :=
    by
    unfold nb055AlphaDummy003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0007 x y) 0))
  have freshness18 : nb055AlphaDummy000 ≠ nb055AlphaDummy001 :=
    by
    unfold nb055AlphaDummy000 nb055AlphaDummy001
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

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0004`. -/
@[expose]
noncomputable def nb055SplitAlpha0004 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy044), (nb055AlphaDummy045 x y)),
        ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy044))
          (Class.cab (nb055AlphaDummy014)
            (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
              (Wff.classEq (Class.cv (nb055AlphaDummy014))
                (synCun (synCphi (Class.cv (nb055AlphaDummy015))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb055AlphaDummy044))
            (Class.cab (nb055AlphaDummy014)
              (synWrex (nb055AlphaDummy015) (Class.cv (nb055AlphaDummy001))
                (Wff.classEq (Class.cv (nb055AlphaDummy014))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy015)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy045 x y))
          (Class.cab (nb055AlphaDummy016 x y)
            (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055AlphaDummy045 x y))
            (Class.cab (nb055AlphaDummy016 x y)
              (synWrex (nb055AlphaDummy017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055AlphaDummy016 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy017 x y)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (nb055VariableOccurrence0 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb055AlphaDummy000))).fv ∪
                      ((Class.cv (nb055AlphaDummy001))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055SplitAlpha0003 x y)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055SplitAlpha0003 x y)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy046), (nb055AlphaDummy047 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy044), (nb055AlphaDummy045 x y)),
                          ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
                          ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                          ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                          ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
                          ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (nb055VariableOccurrence0 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb055AlphaDummy000))).fv ∪
                        ((Class.cv (nb055AlphaDummy001))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055SplitAlpha0003 x y)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055SplitAlpha0003 x y)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb055AlphaDummy046), (nb055AlphaDummy047 x y)),
                            ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                            ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                            ((nb055AlphaDummy044), (nb055AlphaDummy045 x y)),
                            ((nb055AlphaDummy018), (nb055AlphaDummy019 x y)),
                            ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                            ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                            ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
                            ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                            ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                            ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                            ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0005`. -/
@[expose]
noncomputable def nb055SplitAlpha0005 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy058), (nb055AlphaDummy061 x y)),
        ((nb055AlphaDummy057), (nb055AlphaDummy060 x y)),
        ((nb055AlphaDummy056), (nb055AlphaDummy059 x y)),
        ((nb055AlphaDummy054), (nb055AlphaDummy055 x y)),
        ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
        ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)),
        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy056))
            (synCun (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy059 x y))
            (synCun (Class.cv (nb055AlphaDummy060 x y))
              (Class.cv (nb055AlphaDummy061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy058), (nb055AlphaDummy061 x y)),
          ((nb055AlphaDummy057), (nb055AlphaDummy060 x y)),
          ((nb055AlphaDummy056), (nb055AlphaDummy059 x y)),
          ((nb055AlphaDummy054), (nb055AlphaDummy055 x y)),
          ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
          ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)),
          ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
          ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
          ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
          ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0006`. -/
@[expose]
noncomputable def nb055SplitAlpha0006 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy007))
          (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001))))
        (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy006))
            (synCphi (Class.cv (nb055AlphaDummy007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy009 x y))
          (synCop (Class.cv x) (Class.cv y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
            (synCphi (Class.cv (nb055AlphaDummy009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb055_variable_occurrence_1 x y dv_x_y))
                            (nb055SplitAlpha0001 x y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb055_variable_occurrence_1 x y dv_x_y))
                            (nb055SplitAlpha0001 x y)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb055SplitAlpha0004 x y)))))))))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((synCop (Class.cv (nb055AlphaDummy000))
                    (Class.cv (nb055AlphaDummy001)))).fv ∪
                ((Class.cv (nb055AlphaDummy002))).fv) (by decide)) (freshVar_injective
              (((synCop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb055AlphaDummy003 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb055AlphaDummy007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb055AlphaDummy009 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0064) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0065 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0064) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb055AlphaDummy058),
        (nb055AlphaDummy061 x y)), ((nb055AlphaDummy057), (nb055AlphaDummy060 x y)),
        ((nb055AlphaDummy056), (nb055AlphaDummy059 x y)), ((nb055AlphaDummy054),
        (nb055AlphaDummy055 x y)), ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
        ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)), ((nb055AlphaDummy007),
        (nb055AlphaDummy009 x y)), ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)), ((nb055AlphaDummy010),
        (nb055AlphaDummy011 x y)), ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x), ((nb055AlphaDummy004),
        (nb055AlphaDummy005 x y))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb055SplitAlpha0005 x y))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb055AlphaDummy054), (nb055AlphaDummy055 x y)),
                              ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
                              ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)),
                              ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                              ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                              ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
                              ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                              ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                              ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                              ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb055AlphaDummy054), (nb055AlphaDummy055 x y)),
                              ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
                              ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)),
                              ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                              ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                              ((nb055AlphaDummy012), (nb055AlphaDummy013 x y)),
                              ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                              ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                              ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                              ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part008`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0007`. -/
@[expose]
noncomputable def nb055SplitAlpha0007 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy058), (nb055AlphaDummy061 x y)),
        ((nb055AlphaDummy057), (nb055AlphaDummy060 x y)),
        ((nb055AlphaDummy056), (nb055AlphaDummy059 x y)),
        ((nb055AlphaDummy054), (nb055AlphaDummy055 x y)),
        ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
        ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)),
        ((nb055AlphaDummy076), (nb055AlphaDummy077 x y)),
        ((nb055AlphaDummy074), (nb055AlphaDummy075 x y)),
        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy072), (nb055AlphaDummy073 x y)),
        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy056))
            (synCun (Class.cv (nb055AlphaDummy057)) (Class.cv (nb055AlphaDummy058))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy060 x y))
            (Class.cv (nb055AlphaDummy061 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy059 x y))
            (synCun (Class.cv (nb055AlphaDummy060 x y))
              (Class.cv (nb055AlphaDummy061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy058), (nb055AlphaDummy061 x y)),
          ((nb055AlphaDummy057), (nb055AlphaDummy060 x y)),
          ((nb055AlphaDummy056), (nb055AlphaDummy059 x y)),
          ((nb055AlphaDummy054), (nb055AlphaDummy055 x y)),
          ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
          ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)),
          ((nb055AlphaDummy076), (nb055AlphaDummy077 x y)),
          ((nb055AlphaDummy074), (nb055AlphaDummy075 x y)),
          ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
          ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
          ((nb055AlphaDummy072), (nb055AlphaDummy073 x y)),
          ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0008`. -/
@[expose]
noncomputable def nb055SplitAlpha0008 (x : Var) (y : Var) :
    TAlphaClass
      [((nb055AlphaDummy076), (nb055AlphaDummy077 x y)),
        ((nb055AlphaDummy074), (nb055AlphaDummy075 x y)),
        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
        ((nb055AlphaDummy072), (nb055AlphaDummy073 x y)),
        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Class.cab (nb055AlphaDummy051)
        (synWrex (nb055AlphaDummy050) (Class.cv (nb055AlphaDummy007))
          (Wff.classEq (Class.cv (nb055AlphaDummy051))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy050)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy050)) (synC1c))
              (Class.cv (nb055AlphaDummy050))))))
      (Class.cab (nb055AlphaDummy053 x y)
        (synWrex (nb055AlphaDummy052 x y) (Class.cv (nb055AlphaDummy009 x y))
          (Wff.classEq (Class.cv (nb055AlphaDummy053 x y))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy052 x y)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy052 x y)) (synC1c))
              (Class.cv (nb055AlphaDummy052 x y)))))) :=
  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 1)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0090) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0091 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0088) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0089 x y) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (nb055AlphaDummy007))).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy009 x y))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0064) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0065 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0064) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0065 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0062) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb055AlphaDummy058), (nb055AlphaDummy061 x y)),
                                    ((nb055AlphaDummy057), (nb055AlphaDummy060 x y)),
                                    ((nb055AlphaDummy056), (nb055AlphaDummy059 x y)),
                                    ((nb055AlphaDummy054), (nb055AlphaDummy055 x y)),
                                    ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
                                    ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)),
                                    ((nb055AlphaDummy076), (nb055AlphaDummy077 x y)),
                                    ((nb055AlphaDummy074), (nb055AlphaDummy075 x y)),
                                    ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                                    ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                                    ((nb055AlphaDummy072), (nb055AlphaDummy073 x y)),
                                    ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                                    ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                                    ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                                    ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                                  (synC1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb055SplitAlpha0007 x y))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((nb055AlphaDummy054), (nb055AlphaDummy055 x y)),
                        ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
                        ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)),
                        ((nb055AlphaDummy076), (nb055AlphaDummy077 x y)),
                        ((nb055AlphaDummy074), (nb055AlphaDummy075 x y)),
                        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                        ((nb055AlphaDummy072), (nb055AlphaDummy073 x y)),
                        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                      (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((nb055AlphaDummy054), (nb055AlphaDummy055 x y)),
                        ((nb055AlphaDummy050), (nb055AlphaDummy052 x y)),
                        ((nb055AlphaDummy051), (nb055AlphaDummy053 x y)),
                        ((nb055AlphaDummy076), (nb055AlphaDummy077 x y)),
                        ((nb055AlphaDummy074), (nb055AlphaDummy075 x y)),
                        ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                        ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                        ((nb055AlphaDummy072), (nb055AlphaDummy073 x y)),
                        ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                      (synCnnc) (by simp only [fv_syn_cnnc])))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_variable_occurrence_2`. -/
@[expose]
noncomputable def nb055_variable_occurrence_2 (x y : Var) :
    TAlphaClass
      [(nb055AlphaDummy007, (nb055AlphaDummy009 x y)),
        (nb055AlphaDummy006, (nb055AlphaDummy008 x y)),
        (nb055AlphaDummy072, (nb055AlphaDummy073 x y)),
        (nb055AlphaDummy010, (nb055AlphaDummy011 x y)),
        (nb055AlphaDummy002, (nb055AlphaDummy003 x y)), (nb055AlphaDummy001, y),
        (nb055AlphaDummy000, x), (nb055AlphaDummy004, (nb055AlphaDummy005 x y))]
      (Class.cv nb055AlphaDummy002) (Class.cv (nb055AlphaDummy003 x y)) :=
  by
  have freshness0 : nb055AlphaDummy002 ≠ nb055AlphaDummy007 :=
    by
    unfold nb055AlphaDummy007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1))
  have freshness1 : (nb055AlphaDummy003 x y) ≠ (nb055AlphaDummy009 x y) :=
    by
    unfold nb055AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1))
  have freshness2 : nb055AlphaDummy002 ≠ nb055AlphaDummy006 :=
    by
    unfold nb055AlphaDummy006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0))
  have freshness3 : (nb055AlphaDummy003 x y) ≠ (nb055AlphaDummy008 x y) :=
    by
    unfold nb055AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0))
  have freshness4 : nb055AlphaDummy002 ≠ nb055AlphaDummy072 :=
    by
    unfold nb055AlphaDummy072
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0086) 0))
  have freshness5 : (nb055AlphaDummy003 x y) ≠ (nb055AlphaDummy073 x y) :=
    by
    unfold nb055AlphaDummy073
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0087 x y) 0))
  have freshness6 : nb055AlphaDummy002 ≠ nb055AlphaDummy010 :=
    by
    unfold nb055AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0083) 0))
  have freshness7 : (nb055AlphaDummy003 x y) ≠ (nb055AlphaDummy011 x y) :=
    by
    unfold nb055AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0085 x y) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.here _ _ _))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0009`. -/
@[expose]
noncomputable def nb055SplitAlpha0009 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy010)) (synCcompl
            (Class.cab (nb055AlphaDummy006) (synWrex (nb055AlphaDummy007)
                (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
                (Wff.classEq (Class.cv (nb055AlphaDummy006))
                  (synCphi (Class.cv (nb055AlphaDummy007)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055AlphaDummy010)) (synCcompl
              (Class.cab (nb055AlphaDummy006)
                (synWrex (nb055AlphaDummy007) (Class.cv (nb055AlphaDummy002))
                  (Wff.classEq (Class.cv (nb055AlphaDummy006))
                    (synCun (synCphi (Class.cv (nb055AlphaDummy007)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy011 x y)) (synCcompl
            (Class.cab (nb055AlphaDummy008 x y)
              (synWrex (nb055AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                  (synCphi (Class.cv (nb055AlphaDummy009 x y)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055AlphaDummy011 x y)) (synCcompl
              (Class.cab (nb055AlphaDummy008 x y) (synWrex (nb055AlphaDummy009 x y)
                  (Class.cv (nb055AlphaDummy003 x y))
                  (Wff.classEq (Class.cv (nb055AlphaDummy008 x y))
                    (synCun (synCphi (Class.cv (nb055AlphaDummy009 x y)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb055SplitAlpha0006 x y dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb055SplitAlpha0006 x y dv_x_y)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb055_variable_occurrence_2 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((synCop (Class.cv (nb055AlphaDummy000))
                                    (Class.cv (nb055AlphaDummy001)))).fv ∪
                                ((Class.cv (nb055AlphaDummy002))).fv) (by decide))
                            (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb055AlphaDummy003 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb055SplitAlpha0008 x y)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb055SplitAlpha0008 x y))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb055AlphaDummy074), (nb055AlphaDummy075 x y)),
                                    ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                                    ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                                    ((nb055AlphaDummy072), (nb055AlphaDummy073 x y)),
                                    ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                                    ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                                    ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                                    ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb055_variable_occurrence_2 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((synCop (Class.cv (nb055AlphaDummy000))
                                    (Class.cv (nb055AlphaDummy001)))).fv ∪
                                ((Class.cv (nb055AlphaDummy002))).fv) (by decide))
                            (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb055AlphaDummy003 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb055SplitAlpha0008 x y)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb055SplitAlpha0008 x y))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb055AlphaDummy074), (nb055AlphaDummy075 x y)),
                                    ((nb055AlphaDummy007), (nb055AlphaDummy009 x y)),
                                    ((nb055AlphaDummy006), (nb055AlphaDummy008 x y)),
                                    ((nb055AlphaDummy072), (nb055AlphaDummy073 x y)),
                                    ((nb055AlphaDummy010), (nb055AlphaDummy011 x y)),
                                    ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                                    ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                                    ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part009`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0010`. -/
@[expose]
noncomputable def nb055SplitAlpha0010 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy098), (nb055AlphaDummy101 x y)),
        ((nb055AlphaDummy097), (nb055AlphaDummy100 x y)),
        ((nb055AlphaDummy096), (nb055AlphaDummy099 x y)),
        ((nb055AlphaDummy094), (nb055AlphaDummy095 x y)),
        ((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
        ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
        ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
        ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
        ((nb055AlphaDummy088), (nb055AlphaDummy089 x y)),
        ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy096))
            (synCun (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy099 x y))
            (synCun (Class.cv (nb055AlphaDummy100 x y))
              (Class.cv (nb055AlphaDummy101 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0111 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0109 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0115 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0113 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0111 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0109 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0115 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0113 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy098), (nb055AlphaDummy101 x y)),
          ((nb055AlphaDummy097), (nb055AlphaDummy100 x y)),
          ((nb055AlphaDummy096), (nb055AlphaDummy099 x y)),
          ((nb055AlphaDummy094), (nb055AlphaDummy095 x y)),
          ((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
          ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
          ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
          ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
          ((nb055AlphaDummy088), (nb055AlphaDummy089 x y)),
          ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0119 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0117 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0119 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0117 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0123 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0121 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0123 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0121 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0011`. -/
@[expose]
noncomputable def nb055SplitAlpha0011 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
        ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
        ((nb055AlphaDummy088), (nb055AlphaDummy089 x y)),
        ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.classEq (Class.cv (nb055AlphaDummy082))
        (synCphi (Class.cv (nb055AlphaDummy083))))
      (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
        (synCphi (Class.cv (nb055AlphaDummy085 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
            ((Class.cv (nb055AlphaDummy017 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0102) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0103 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0102) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0103 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb055AlphaDummy083))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb055AlphaDummy085 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0106) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0107 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0106) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0107 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0104) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed [((nb055AlphaDummy098),
                                        (nb055AlphaDummy101 x y)), ((nb055AlphaDummy097),
                                        (nb055AlphaDummy100 x y)), ((nb055AlphaDummy096),
                                        (nb055AlphaDummy099 x y)), ((nb055AlphaDummy094),
                                        (nb055AlphaDummy095 x y)), ((nb055AlphaDummy090),
                                        (nb055AlphaDummy092 x y)), ((nb055AlphaDummy091),
                                        (nb055AlphaDummy093 x y)), ((nb055AlphaDummy083),
                                        (nb055AlphaDummy085 x y)), ((nb055AlphaDummy082),
                                        (nb055AlphaDummy084 x y)), ((nb055AlphaDummy088),
                                        (nb055AlphaDummy089 x y)), ((nb055AlphaDummy086),
                                        (nb055AlphaDummy087 x y)), ((nb055AlphaDummy015),
                                        (nb055AlphaDummy017 x y)), ((nb055AlphaDummy014),
                                        (nb055AlphaDummy016 x y)), ((nb055AlphaDummy080),
                                        (nb055AlphaDummy081 x y)), ((nb055AlphaDummy002),
                                        (nb055AlphaDummy003 x y)),
                                      ((nb055AlphaDummy001), y),
                                      ((nb055AlphaDummy000), x), ((nb055AlphaDummy004),
                                        (nb055AlphaDummy005 x y))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb055SplitAlpha0010 x y))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy094), (nb055AlphaDummy095 x y)),
                          ((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
                          ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
                          ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
                          ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
                          ((nb055AlphaDummy088), (nb055AlphaDummy089 x y)),
                          ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy094), (nb055AlphaDummy095 x y)),
                          ((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
                          ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
                          ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
                          ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
                          ((nb055AlphaDummy088), (nb055AlphaDummy089 x y)),
                          ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0012`. -/
@[expose]
noncomputable def nb055SplitAlpha0012 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy098), (nb055AlphaDummy101 x y)),
        ((nb055AlphaDummy097), (nb055AlphaDummy100 x y)),
        ((nb055AlphaDummy096), (nb055AlphaDummy099 x y)),
        ((nb055AlphaDummy094), (nb055AlphaDummy095 x y)),
        ((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
        ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
        ((nb055AlphaDummy116), (nb055AlphaDummy117 x y)),
        ((nb055AlphaDummy114), (nb055AlphaDummy115 x y)),
        ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
        ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
        ((nb055AlphaDummy112), (nb055AlphaDummy113 x y)),
        ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy096))
            (synCun (Class.cv (nb055AlphaDummy097)) (Class.cv (nb055AlphaDummy098))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy100 x y))
            (Class.cv (nb055AlphaDummy101 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy099 x y))
            (synCun (Class.cv (nb055AlphaDummy100 x y))
              (Class.cv (nb055AlphaDummy101 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0111 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0109 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0115 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0113 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0111 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0109 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0115 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0113 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy098), (nb055AlphaDummy101 x y)),
          ((nb055AlphaDummy097), (nb055AlphaDummy100 x y)),
          ((nb055AlphaDummy096), (nb055AlphaDummy099 x y)),
          ((nb055AlphaDummy094), (nb055AlphaDummy095 x y)),
          ((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
          ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
          ((nb055AlphaDummy116), (nb055AlphaDummy117 x y)),
          ((nb055AlphaDummy114), (nb055AlphaDummy115 x y)),
          ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
          ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
          ((nb055AlphaDummy112), (nb055AlphaDummy113 x y)),
          ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0119 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0117 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0119 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0117 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy090))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy092 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0123 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0121 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0123 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0121 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0013`. -/
@[expose]
noncomputable def nb055SplitAlpha0013 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
        ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
        ((nb055AlphaDummy116), (nb055AlphaDummy117 x y)),
        ((nb055AlphaDummy114), (nb055AlphaDummy115 x y)),
        ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
        ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
        ((nb055AlphaDummy112), (nb055AlphaDummy113 x y)),
        ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy090))
          (Class.cv (nb055AlphaDummy083))) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy091))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy090)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy090)) (synC1c))
              (Class.cv (nb055AlphaDummy090))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy092 x y))
          (Class.cv (nb055AlphaDummy085 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy093 x y))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy092 x y)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy092 x y)) (synC1c))
              (Class.cv (nb055AlphaDummy092 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0102) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0103 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0102) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0103 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0132) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0133 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0130) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0131 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy083))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb055AlphaDummy085 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0106) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0107 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0106) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0107 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0104) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb055AlphaDummy098), (nb055AlphaDummy101 x y)),
                                  ((nb055AlphaDummy097), (nb055AlphaDummy100 x y)),
                                  ((nb055AlphaDummy096), (nb055AlphaDummy099 x y)),
                                  ((nb055AlphaDummy094), (nb055AlphaDummy095 x y)),
                                  ((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
                                  ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
                                  ((nb055AlphaDummy116), (nb055AlphaDummy117 x y)),
                                  ((nb055AlphaDummy114), (nb055AlphaDummy115 x y)),
                                  ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
                                  ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
                                  ((nb055AlphaDummy112), (nb055AlphaDummy113 x y)),
                                  ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
                                  ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                                  ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                                  ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                                  ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                                  ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                                  ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb055SplitAlpha0012 x y))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb055AlphaDummy094), (nb055AlphaDummy095 x y)),
                      ((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
                      ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
                      ((nb055AlphaDummy116), (nb055AlphaDummy117 x y)),
                      ((nb055AlphaDummy114), (nb055AlphaDummy115 x y)),
                      ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
                      ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
                      ((nb055AlphaDummy112), (nb055AlphaDummy113 x y)),
                      ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
                      ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                      ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                      ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                      ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                      ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                      ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb055AlphaDummy094), (nb055AlphaDummy095 x y)),
                      ((nb055AlphaDummy090), (nb055AlphaDummy092 x y)),
                      ((nb055AlphaDummy091), (nb055AlphaDummy093 x y)),
                      ((nb055AlphaDummy116), (nb055AlphaDummy117 x y)),
                      ((nb055AlphaDummy114), (nb055AlphaDummy115 x y)),
                      ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
                      ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
                      ((nb055AlphaDummy112), (nb055AlphaDummy113 x y)),
                      ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
                      ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                      ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                      ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                      ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                      ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                      ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part010`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0014`. -/
@[expose]
noncomputable def nb055SplitAlpha0014 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy112), (nb055AlphaDummy113 x y)),
        ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy112))
          (Class.cab (nb055AlphaDummy082)
            (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy082))
                (synCun (synCphi (Class.cv (nb055AlphaDummy083))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb055AlphaDummy112))
            (Class.cab (nb055AlphaDummy082)
              (synWrex (nb055AlphaDummy083) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy082))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy083)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy113 x y))
          (Class.cab (nb055AlphaDummy084 x y)
            (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055AlphaDummy113 x y))
            (Class.cab (nb055AlphaDummy084 x y)
              (synWrex (nb055AlphaDummy085 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy084 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy085 x y)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0128) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0129 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0125) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0127 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb055AlphaDummy014))).fv ∪
                      ((Class.cv (nb055AlphaDummy015))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
                      ((Class.cv (nb055AlphaDummy017 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055SplitAlpha0013 x y)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055SplitAlpha0013 x y)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy114), (nb055AlphaDummy115 x y)),
                          ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
                          ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
                          ((nb055AlphaDummy112), (nb055AlphaDummy113 x y)),
                          ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0128) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0129 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0125) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0127 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb055AlphaDummy014))).fv ∪
                        ((Class.cv (nb055AlphaDummy015))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
                        ((Class.cv (nb055AlphaDummy017 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055SplitAlpha0013 x y)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055SplitAlpha0013 x y)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb055AlphaDummy114), (nb055AlphaDummy115 x y)),
                            ((nb055AlphaDummy083), (nb055AlphaDummy085 x y)),
                            ((nb055AlphaDummy082), (nb055AlphaDummy084 x y)),
                            ((nb055AlphaDummy112), (nb055AlphaDummy113 x y)),
                            ((nb055AlphaDummy086), (nb055AlphaDummy087 x y)),
                            ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                            ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                            ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                            ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                            ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                            ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0015`. -/
@[expose]
noncomputable def nb055SplitAlpha0015 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy134), (nb055AlphaDummy137 x y)),
        ((nb055AlphaDummy133), (nb055AlphaDummy136 x y)),
        ((nb055AlphaDummy132), (nb055AlphaDummy135 x y)),
        ((nb055AlphaDummy130), (nb055AlphaDummy131 x y)),
        ((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
        ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
        ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
        ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
        ((nb055AlphaDummy124), (nb055AlphaDummy125 x y)),
        ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy132))
            (synCun (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy135 x y))
            (synCun (Class.cv (nb055AlphaDummy136 x y))
              (Class.cv (nb055AlphaDummy137 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy134), (nb055AlphaDummy137 x y)),
          ((nb055AlphaDummy133), (nb055AlphaDummy136 x y)),
          ((nb055AlphaDummy132), (nb055AlphaDummy135 x y)),
          ((nb055AlphaDummy130), (nb055AlphaDummy131 x y)),
          ((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
          ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
          ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
          ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
          ((nb055AlphaDummy124), (nb055AlphaDummy125 x y)),
          ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0016`. -/
@[expose]
noncomputable def nb055SplitAlpha0016 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
        ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
        ((nb055AlphaDummy124), (nb055AlphaDummy125 x y)),
        ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.classEq (Class.cv (nb055AlphaDummy118))
        (synCphi (Class.cv (nb055AlphaDummy119))))
      (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
        (synCphi (Class.cv (nb055AlphaDummy121 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb055AlphaDummy014))).fv ∪ ((Class.cv (nb055AlphaDummy078))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
            ((Class.cv (nb055AlphaDummy079 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb055AlphaDummy119))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb055AlphaDummy121 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0144) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0145 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0144) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0145 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0142) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed [((nb055AlphaDummy134),
                                        (nb055AlphaDummy137 x y)), ((nb055AlphaDummy133),
                                        (nb055AlphaDummy136 x y)), ((nb055AlphaDummy132),
                                        (nb055AlphaDummy135 x y)), ((nb055AlphaDummy130),
                                        (nb055AlphaDummy131 x y)), ((nb055AlphaDummy126),
                                        (nb055AlphaDummy128 x y)), ((nb055AlphaDummy127),
                                        (nb055AlphaDummy129 x y)), ((nb055AlphaDummy119),
                                        (nb055AlphaDummy121 x y)), ((nb055AlphaDummy118),
                                        (nb055AlphaDummy120 x y)), ((nb055AlphaDummy124),
                                        (nb055AlphaDummy125 x y)), ((nb055AlphaDummy122),
                                        (nb055AlphaDummy123 x y)), ((nb055AlphaDummy078),
                                        (nb055AlphaDummy079 x y)), ((nb055AlphaDummy015),
                                        (nb055AlphaDummy017 x y)), ((nb055AlphaDummy014),
                                        (nb055AlphaDummy016 x y)), ((nb055AlphaDummy080),
                                        (nb055AlphaDummy081 x y)), ((nb055AlphaDummy002),
                                        (nb055AlphaDummy003 x y)),
                                      ((nb055AlphaDummy001), y),
                                      ((nb055AlphaDummy000), x), ((nb055AlphaDummy004),
                                        (nb055AlphaDummy005 x y))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb055SplitAlpha0015 x y))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy130), (nb055AlphaDummy131 x y)),
                          ((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
                          ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
                          ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
                          ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
                          ((nb055AlphaDummy124), (nb055AlphaDummy125 x y)),
                          ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
                          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy130), (nb055AlphaDummy131 x y)),
                          ((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
                          ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
                          ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
                          ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
                          ((nb055AlphaDummy124), (nb055AlphaDummy125 x y)),
                          ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
                          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part011`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0017`. -/
@[expose]
noncomputable def nb055SplitAlpha0017 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy134), (nb055AlphaDummy137 x y)),
        ((nb055AlphaDummy133), (nb055AlphaDummy136 x y)),
        ((nb055AlphaDummy132), (nb055AlphaDummy135 x y)),
        ((nb055AlphaDummy130), (nb055AlphaDummy131 x y)),
        ((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
        ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
        ((nb055AlphaDummy152), (nb055AlphaDummy153 x y)),
        ((nb055AlphaDummy150), (nb055AlphaDummy151 x y)),
        ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
        ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
        ((nb055AlphaDummy148), (nb055AlphaDummy149 x y)),
        ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy132))
            (synCun (Class.cv (nb055AlphaDummy133)) (Class.cv (nb055AlphaDummy134))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy136 x y))
            (Class.cv (nb055AlphaDummy137 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy135 x y))
            (synCun (Class.cv (nb055AlphaDummy136 x y))
              (Class.cv (nb055AlphaDummy137 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy134), (nb055AlphaDummy137 x y)),
          ((nb055AlphaDummy133), (nb055AlphaDummy136 x y)),
          ((nb055AlphaDummy132), (nb055AlphaDummy135 x y)),
          ((nb055AlphaDummy130), (nb055AlphaDummy131 x y)),
          ((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
          ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
          ((nb055AlphaDummy152), (nb055AlphaDummy153 x y)),
          ((nb055AlphaDummy150), (nb055AlphaDummy151 x y)),
          ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
          ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
          ((nb055AlphaDummy148), (nb055AlphaDummy149 x y)),
          ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy126))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy128 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0018`. -/
@[expose]
noncomputable def nb055SplitAlpha0018 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
        ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
        ((nb055AlphaDummy152), (nb055AlphaDummy153 x y)),
        ((nb055AlphaDummy150), (nb055AlphaDummy151 x y)),
        ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
        ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
        ((nb055AlphaDummy148), (nb055AlphaDummy149 x y)),
        ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy126))
          (Class.cv (nb055AlphaDummy119))) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy127))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy126)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy126)) (synC1c))
              (Class.cv (nb055AlphaDummy126))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy128 x y))
          (Class.cv (nb055AlphaDummy121 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy129 x y))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy128 x y)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy128 x y)) (synC1c))
              (Class.cv (nb055AlphaDummy128 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0170) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0171 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0168) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0169 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy119))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb055AlphaDummy121 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0144) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0145 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0144) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0145 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb055AlphaDummy134), (nb055AlphaDummy137 x y)),
                                  ((nb055AlphaDummy133), (nb055AlphaDummy136 x y)),
                                  ((nb055AlphaDummy132), (nb055AlphaDummy135 x y)),
                                  ((nb055AlphaDummy130), (nb055AlphaDummy131 x y)),
                                  ((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
                                  ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
                                  ((nb055AlphaDummy152), (nb055AlphaDummy153 x y)),
                                  ((nb055AlphaDummy150), (nb055AlphaDummy151 x y)),
                                  ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
                                  ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
                                  ((nb055AlphaDummy148), (nb055AlphaDummy149 x y)),
                                  ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
                                  ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                                  ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                                  ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                                  ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                                  ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                                  ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                                  ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb055SplitAlpha0017 x y))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb055AlphaDummy130), (nb055AlphaDummy131 x y)),
                      ((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
                      ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
                      ((nb055AlphaDummy152), (nb055AlphaDummy153 x y)),
                      ((nb055AlphaDummy150), (nb055AlphaDummy151 x y)),
                      ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
                      ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
                      ((nb055AlphaDummy148), (nb055AlphaDummy149 x y)),
                      ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
                      ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                      ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                      ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                      ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                      ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                      ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                      ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb055AlphaDummy130), (nb055AlphaDummy131 x y)),
                      ((nb055AlphaDummy126), (nb055AlphaDummy128 x y)),
                      ((nb055AlphaDummy127), (nb055AlphaDummy129 x y)),
                      ((nb055AlphaDummy152), (nb055AlphaDummy153 x y)),
                      ((nb055AlphaDummy150), (nb055AlphaDummy151 x y)),
                      ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
                      ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
                      ((nb055AlphaDummy148), (nb055AlphaDummy149 x y)),
                      ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
                      ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                      ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                      ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                      ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                      ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                      ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                      ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0019`. -/
@[expose]
noncomputable def nb055SplitAlpha0019 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy148), (nb055AlphaDummy149 x y)),
        ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy148))
          (Class.cab (nb055AlphaDummy118)
            (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
              (Wff.classEq (Class.cv (nb055AlphaDummy118))
                (synCun (synCphi (Class.cv (nb055AlphaDummy119))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb055AlphaDummy148))
            (Class.cab (nb055AlphaDummy118)
              (synWrex (nb055AlphaDummy119) (Class.cv (nb055AlphaDummy078))
                (Wff.classEq (Class.cv (nb055AlphaDummy118))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy119)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy149 x y))
          (Class.cab (nb055AlphaDummy120 x y)
            (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055AlphaDummy149 x y))
            (Class.cab (nb055AlphaDummy120 x y)
              (synWrex (nb055AlphaDummy121 x y) (Class.cv (nb055AlphaDummy079 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy120 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy121 x y)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0166) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0167 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0163) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0165 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb055AlphaDummy014))).fv ∪
                      ((Class.cv (nb055AlphaDummy078))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
                      ((Class.cv (nb055AlphaDummy079 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055SplitAlpha0018 x y)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055SplitAlpha0018 x y)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy150), (nb055AlphaDummy151 x y)),
                          ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
                          ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
                          ((nb055AlphaDummy148), (nb055AlphaDummy149 x y)),
                          ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
                          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0166) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0167 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0163) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0165 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb055AlphaDummy014))).fv ∪
                        ((Class.cv (nb055AlphaDummy078))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb055AlphaDummy016 x y))).fv ∪
                        ((Class.cv (nb055AlphaDummy079 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055SplitAlpha0018 x y)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055SplitAlpha0018 x y)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb055AlphaDummy150), (nb055AlphaDummy151 x y)),
                            ((nb055AlphaDummy119), (nb055AlphaDummy121 x y)),
                            ((nb055AlphaDummy118), (nb055AlphaDummy120 x y)),
                            ((nb055AlphaDummy148), (nb055AlphaDummy149 x y)),
                            ((nb055AlphaDummy122), (nb055AlphaDummy123 x y)),
                            ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                            ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                            ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                            ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                            ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                            ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                            ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0020`. -/
@[expose]
noncomputable def nb055SplitAlpha0020 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy170), (nb055AlphaDummy173 x y)),
        ((nb055AlphaDummy169), (nb055AlphaDummy172 x y)),
        ((nb055AlphaDummy168), (nb055AlphaDummy171 x y)),
        ((nb055AlphaDummy166), (nb055AlphaDummy167 x y)),
        ((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
        ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
        ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
        ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
        ((nb055AlphaDummy160), (nb055AlphaDummy161 x y)),
        ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy168))
            (synCun (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy171 x y))
            (synCun (Class.cv (nb055AlphaDummy172 x y))
              (Class.cv (nb055AlphaDummy173 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy170), (nb055AlphaDummy173 x y)),
          ((nb055AlphaDummy169), (nb055AlphaDummy172 x y)),
          ((nb055AlphaDummy168), (nb055AlphaDummy171 x y)),
          ((nb055AlphaDummy166), (nb055AlphaDummy167 x y)),
          ((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
          ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
          ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
          ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
          ((nb055AlphaDummy160), (nb055AlphaDummy161 x y)),
          ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part012`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0021`. -/
@[expose]
noncomputable def nb055SplitAlpha0021 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
        ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
        ((nb055AlphaDummy160), (nb055AlphaDummy161 x y)),
        ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.classEq (Class.cv (nb055AlphaDummy154))
        (synCphi (Class.cv (nb055AlphaDummy155))))
      (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
        (synCphi (Class.cv (nb055AlphaDummy157 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb055AlphaDummy078))).fv ∪ ((Class.cv (nb055AlphaDummy015))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
            ((Class.cv (nb055AlphaDummy017 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0180) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0181 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0180) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0181 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb055AlphaDummy155))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb055AlphaDummy157 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0184) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0185 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0184) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0185 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0182) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed [((nb055AlphaDummy170),
                                        (nb055AlphaDummy173 x y)), ((nb055AlphaDummy169),
                                        (nb055AlphaDummy172 x y)), ((nb055AlphaDummy168),
                                        (nb055AlphaDummy171 x y)), ((nb055AlphaDummy166),
                                        (nb055AlphaDummy167 x y)), ((nb055AlphaDummy162),
                                        (nb055AlphaDummy164 x y)), ((nb055AlphaDummy163),
                                        (nb055AlphaDummy165 x y)), ((nb055AlphaDummy155),
                                        (nb055AlphaDummy157 x y)), ((nb055AlphaDummy154),
                                        (nb055AlphaDummy156 x y)), ((nb055AlphaDummy160),
                                        (nb055AlphaDummy161 x y)), ((nb055AlphaDummy158),
                                        (nb055AlphaDummy159 x y)), ((nb055AlphaDummy078),
                                        (nb055AlphaDummy079 x y)), ((nb055AlphaDummy015),
                                        (nb055AlphaDummy017 x y)), ((nb055AlphaDummy014),
                                        (nb055AlphaDummy016 x y)), ((nb055AlphaDummy080),
                                        (nb055AlphaDummy081 x y)), ((nb055AlphaDummy002),
                                        (nb055AlphaDummy003 x y)),
                                      ((nb055AlphaDummy001), y),
                                      ((nb055AlphaDummy000), x), ((nb055AlphaDummy004),
                                        (nb055AlphaDummy005 x y))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb055SplitAlpha0020 x y))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy166), (nb055AlphaDummy167 x y)),
                          ((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
                          ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
                          ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
                          ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
                          ((nb055AlphaDummy160), (nb055AlphaDummy161 x y)),
                          ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
                          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy166), (nb055AlphaDummy167 x y)),
                          ((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
                          ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
                          ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
                          ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
                          ((nb055AlphaDummy160), (nb055AlphaDummy161 x y)),
                          ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
                          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0022`. -/
@[expose]
noncomputable def nb055SplitAlpha0022 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy170), (nb055AlphaDummy173 x y)),
        ((nb055AlphaDummy169), (nb055AlphaDummy172 x y)),
        ((nb055AlphaDummy168), (nb055AlphaDummy171 x y)),
        ((nb055AlphaDummy166), (nb055AlphaDummy167 x y)),
        ((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
        ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
        ((nb055AlphaDummy188), (nb055AlphaDummy189 x y)),
        ((nb055AlphaDummy186), (nb055AlphaDummy187 x y)),
        ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
        ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
        ((nb055AlphaDummy184), (nb055AlphaDummy185 x y)),
        ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb055AlphaDummy168))
            (synCun (Class.cv (nb055AlphaDummy169)) (Class.cv (nb055AlphaDummy170))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb055AlphaDummy172 x y))
            (Class.cv (nb055AlphaDummy173 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy171 x y))
            (synCun (Class.cv (nb055AlphaDummy172 x y))
              (Class.cv (nb055AlphaDummy173 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb055AlphaDummy170), (nb055AlphaDummy173 x y)),
          ((nb055AlphaDummy169), (nb055AlphaDummy172 x y)),
          ((nb055AlphaDummy168), (nb055AlphaDummy171 x y)),
          ((nb055AlphaDummy166), (nb055AlphaDummy167 x y)),
          ((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
          ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
          ((nb055AlphaDummy188), (nb055AlphaDummy189 x y)),
          ((nb055AlphaDummy186), (nb055AlphaDummy187 x y)),
          ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
          ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
          ((nb055AlphaDummy184), (nb055AlphaDummy185 x y)),
          ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy162))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055AlphaDummy164 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0023`. -/
@[expose]
noncomputable def nb055SplitAlpha0023 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
        ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
        ((nb055AlphaDummy188), (nb055AlphaDummy189 x y)),
        ((nb055AlphaDummy186), (nb055AlphaDummy187 x y)),
        ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
        ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
        ((nb055AlphaDummy184), (nb055AlphaDummy185 x y)),
        ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy162))
          (Class.cv (nb055AlphaDummy155))) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy163))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy162)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy162)) (synC1c))
              (Class.cv (nb055AlphaDummy162))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy164 x y))
          (Class.cv (nb055AlphaDummy157 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055AlphaDummy165 x y))
            (synCif (Wff.classMem (Class.cv (nb055AlphaDummy164 x y)) (synCnnc))
              (synCplc (Class.cv (nb055AlphaDummy164 x y)) (synC1c))
              (Class.cv (nb055AlphaDummy164 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0180) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0181 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0180) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0181 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0210) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0211 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0208) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0209 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055AlphaDummy155))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb055AlphaDummy157 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0184) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0185 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0184) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0185 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0182) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb055AlphaDummy170), (nb055AlphaDummy173 x y)),
                                  ((nb055AlphaDummy169), (nb055AlphaDummy172 x y)),
                                  ((nb055AlphaDummy168), (nb055AlphaDummy171 x y)),
                                  ((nb055AlphaDummy166), (nb055AlphaDummy167 x y)),
                                  ((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
                                  ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
                                  ((nb055AlphaDummy188), (nb055AlphaDummy189 x y)),
                                  ((nb055AlphaDummy186), (nb055AlphaDummy187 x y)),
                                  ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
                                  ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
                                  ((nb055AlphaDummy184), (nb055AlphaDummy185 x y)),
                                  ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
                                  ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                                  ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                                  ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                                  ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                                  ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                                  ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                                  ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb055SplitAlpha0022 x y))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb055AlphaDummy166), (nb055AlphaDummy167 x y)),
                      ((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
                      ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
                      ((nb055AlphaDummy188), (nb055AlphaDummy189 x y)),
                      ((nb055AlphaDummy186), (nb055AlphaDummy187 x y)),
                      ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
                      ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
                      ((nb055AlphaDummy184), (nb055AlphaDummy185 x y)),
                      ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
                      ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                      ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                      ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                      ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                      ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                      ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                      ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb055AlphaDummy166), (nb055AlphaDummy167 x y)),
                      ((nb055AlphaDummy162), (nb055AlphaDummy164 x y)),
                      ((nb055AlphaDummy163), (nb055AlphaDummy165 x y)),
                      ((nb055AlphaDummy188), (nb055AlphaDummy189 x y)),
                      ((nb055AlphaDummy186), (nb055AlphaDummy187 x y)),
                      ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
                      ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
                      ((nb055AlphaDummy184), (nb055AlphaDummy185 x y)),
                      ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
                      ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                      ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                      ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                      ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                      ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                      ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                      ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0024`. -/
@[expose]
noncomputable def nb055SplitAlpha0024 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055AlphaDummy184), (nb055AlphaDummy185 x y)),
        ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
        ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy184))
          (Class.cab (nb055AlphaDummy154)
            (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
              (Wff.classEq (Class.cv (nb055AlphaDummy154))
                (synCun (synCphi (Class.cv (nb055AlphaDummy155))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb055AlphaDummy184))
            (Class.cab (nb055AlphaDummy154)
              (synWrex (nb055AlphaDummy155) (Class.cv (nb055AlphaDummy015))
                (Wff.classEq (Class.cv (nb055AlphaDummy154))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy155)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055AlphaDummy185 x y))
          (Class.cab (nb055AlphaDummy156 x y)
            (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
              (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055AlphaDummy185 x y))
            (Class.cab (nb055AlphaDummy156 x y)
              (synWrex (nb055AlphaDummy157 x y) (Class.cv (nb055AlphaDummy017 x y))
                (Wff.classEq (Class.cv (nb055AlphaDummy156 x y))
                  (synCun (synCphi (Class.cv (nb055AlphaDummy157 x y)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0206) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0207 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0203) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0205 x y) 0))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb055AlphaDummy000))).fv ∪
                              ((Class.cv (nb055AlphaDummy001))).fv) (by decide))
                          (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb055AlphaDummy078))).fv ∪
                      ((Class.cv (nb055AlphaDummy015))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
                      ((Class.cv (nb055AlphaDummy017 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055SplitAlpha0023 x y)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055SplitAlpha0023 x y)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb055AlphaDummy186), (nb055AlphaDummy187 x y)),
                          ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
                          ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
                          ((nb055AlphaDummy184), (nb055AlphaDummy185 x y)),
                          ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
                          ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                          ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                          ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                          ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                          ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                          ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                          ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0206) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0207 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0203) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0205 x y) 0))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb055AlphaDummy000))).fv ∪
                                ((Class.cv (nb055AlphaDummy001))).fv) (by decide))
                            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb055AlphaDummy078))).fv ∪
                        ((Class.cv (nb055AlphaDummy015))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb055AlphaDummy079 x y))).fv ∪
                        ((Class.cv (nb055AlphaDummy017 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055SplitAlpha0023 x y)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055SplitAlpha0023 x y)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb055AlphaDummy186), (nb055AlphaDummy187 x y)),
                            ((nb055AlphaDummy155), (nb055AlphaDummy157 x y)),
                            ((nb055AlphaDummy154), (nb055AlphaDummy156 x y)),
                            ((nb055AlphaDummy184), (nb055AlphaDummy185 x y)),
                            ((nb055AlphaDummy158), (nb055AlphaDummy159 x y)),
                            ((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
                            ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
                            ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
                            ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
                            ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                            ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                            ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part013`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb055_compose_occurrence_0`. -/
@[expose]
noncomputable def nb055ComposeOccurrence0 (x y : Var) :
    TAlphaClass
      [(nb055AlphaDummy078, (nb055AlphaDummy079 x y)),
        (nb055AlphaDummy015, (nb055AlphaDummy017 x y)),
        (nb055AlphaDummy014, (nb055AlphaDummy016 x y)),
        (nb055AlphaDummy080, (nb055AlphaDummy081 x y)),
        (nb055AlphaDummy002, (nb055AlphaDummy003 x y)), (nb055AlphaDummy001, y),
        (nb055AlphaDummy000, x), (nb055AlphaDummy004, (nb055AlphaDummy005 x y))]
      (Class.cv nb055AlphaDummy001) (Class.cv y) :=
  by
  have freshness0 : nb055AlphaDummy001 ≠ nb055AlphaDummy078 :=
    by
    unfold nb055AlphaDummy078
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 2))
  have freshness1 : y ≠ (nb055AlphaDummy079 x y) :=
    by
    unfold nb055AlphaDummy079
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 2))
  have freshness2 : nb055AlphaDummy001 ≠ nb055AlphaDummy015 :=
    by
    unfold nb055AlphaDummy015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
  have freshness3 : y ≠ (nb055AlphaDummy017 x y) :=
    by
    unfold nb055AlphaDummy017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
  have freshness4 : nb055AlphaDummy001 ≠ nb055AlphaDummy014 :=
    by
    unfold nb055AlphaDummy014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  have freshness5 : y ≠ (nb055AlphaDummy016 x y) :=
    by
    unfold nb055AlphaDummy016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  have freshness6 : nb055AlphaDummy001 ≠ nb055AlphaDummy080 :=
    by
    unfold nb055AlphaDummy080
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0172) 0))
  have freshness7 : y ≠ (nb055AlphaDummy081 x y) :=
    by
    unfold nb055AlphaDummy081
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0173 x y) 0))
  have freshness8 : nb055AlphaDummy001 ≠ nb055AlphaDummy002 :=
    by
    unfold nb055AlphaDummy002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0042) 0))
  have freshness9 : y ≠ (nb055AlphaDummy003 x y) :=
    by
    unfold nb055AlphaDummy003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0043 x y) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7
                (TAlphaVar.there freshness8 freshness9 (TAlphaVar.here _ _ _)))))))

/-- Checked nominal proof certificate identified upstream as `nb055_compose_occurrence_1`. -/
@[expose]
noncomputable def nb055_compose_occurrence_1 (x y : Var) (dv_x_y : x ≠ y) :
    TAlphaClass
      [(nb055AlphaDummy078, (nb055AlphaDummy079 x y)),
        (nb055AlphaDummy015, (nb055AlphaDummy017 x y)),
        (nb055AlphaDummy014, (nb055AlphaDummy016 x y)),
        (nb055AlphaDummy080, (nb055AlphaDummy081 x y)),
        (nb055AlphaDummy002, (nb055AlphaDummy003 x y)), (nb055AlphaDummy001, y),
        (nb055AlphaDummy000, x), (nb055AlphaDummy004, (nb055AlphaDummy005 x y))]
      (Class.cv nb055AlphaDummy000) (Class.cv x) :=
  by
  have freshness0 : nb055AlphaDummy000 ≠ nb055AlphaDummy078 :=
    by
    unfold nb055AlphaDummy078
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 2))
  have freshness1 : x ≠ (nb055AlphaDummy079 x y) :=
    by
    unfold nb055AlphaDummy079
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 2))
  have freshness2 : nb055AlphaDummy000 ≠ nb055AlphaDummy015 :=
    by
    unfold nb055AlphaDummy015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
  have freshness3 : x ≠ (nb055AlphaDummy017 x y) :=
    by
    unfold nb055AlphaDummy017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
  have freshness4 : nb055AlphaDummy000 ≠ nb055AlphaDummy014 :=
    by
    unfold nb055AlphaDummy014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  have freshness5 : x ≠ (nb055AlphaDummy016 x y) :=
    by
    unfold nb055AlphaDummy016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  have freshness6 : nb055AlphaDummy000 ≠ nb055AlphaDummy080 :=
    by
    unfold nb055AlphaDummy080
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0212) 0))
  have freshness7 : x ≠ (nb055AlphaDummy081 x y) :=
    by
    unfold nb055AlphaDummy081
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0213 x y) 0))
  have freshness8 : nb055AlphaDummy000 ≠ nb055AlphaDummy002 :=
    by
    unfold nb055AlphaDummy002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0006) 0))
  have freshness9 : x ≠ (nb055AlphaDummy003 x y) :=
    by
    unfold nb055AlphaDummy003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0007 x y) 0))
  have freshness10 : nb055AlphaDummy000 ≠ nb055AlphaDummy001 :=
    by
    unfold nb055AlphaDummy000 nb055AlphaDummy001
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness11 : x ≠ y := by exact dv_x_y
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11 (TAlphaVar.here _ _ _))))))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0025`. -/
@[expose]
noncomputable def nb055SplitAlpha0025 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb055AlphaDummy078), (nb055AlphaDummy079 x y)),
        ((nb055AlphaDummy015), (nb055AlphaDummy017 x y)),
        ((nb055AlphaDummy014), (nb055AlphaDummy016 x y)),
        ((nb055AlphaDummy080), (nb055AlphaDummy081 x y)),
        ((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (synWbr (Class.cv (nb055AlphaDummy014)) (Class.cv (nb055AlphaDummy001))
          (Class.cv (nb055AlphaDummy078))) (Wff.neg
          (synWbr (Class.cv (nb055AlphaDummy078)) (Class.cv (nb055AlphaDummy000))
            (Class.cv (nb055AlphaDummy015)))))
      (Wff.imp (synWbr (Class.cv (nb055AlphaDummy016 x y)) (Class.cv y)
          (Class.cv (nb055AlphaDummy079 x y))) (Wff.neg
          (synWbr (Class.cv (nb055AlphaDummy079 x y)) (Class.cv x)
            (Class.cv (nb055AlphaDummy017 x y))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0134) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0136 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0134) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0136 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0138) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0139 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0135) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0137 x y) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv)
        (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb055AlphaDummy000))).fv ∪
        ((Class.cv (nb055AlphaDummy001))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb055SplitAlpha0016 x y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0134) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0136 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0134) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0136 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0138) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0139 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0135) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0137 x y) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv)
        (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb055AlphaDummy000))).fv ∪
        ((Class.cv (nb055AlphaDummy001))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb055SplitAlpha0016 x y)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb055SplitAlpha0019 x y))))))))
      (nb055ComposeOccurrence0 x y)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0174) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0176 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0174) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0176 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0178) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0179 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0175) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0177 x y) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb055SplitAlpha0021 x y)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0174) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0176 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0174) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0176 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0178) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0179 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0175) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0177 x y) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb055SplitAlpha0021 x y)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb055SplitAlpha0024 x y))))))))
        (nb055_compose_occurrence_1 x y dv_x_y))))

/-- Checked nominal proof certificate identified upstream as `nb055_compose_occurrence_2`. -/
@[expose]
noncomputable def nb055_compose_occurrence_2 (x y : Var) :
    TAlphaClass
      [(nb055AlphaDummy002, (nb055AlphaDummy003 x y)), (nb055AlphaDummy001, y),
        (nb055AlphaDummy000, x), (nb055AlphaDummy004, (nb055AlphaDummy005 x y))]
      (Class.cv nb055AlphaDummy004) (Class.cv (nb055AlphaDummy005 x y)) :=
  by
  have freshness0 : nb055AlphaDummy004 ≠ nb055AlphaDummy002 :=
    by
    unfold nb055AlphaDummy004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0004) 0)))
  have freshness1 : (nb055AlphaDummy005 x y) ≠ (nb055AlphaDummy003 x y) :=
    by
    unfold nb055AlphaDummy005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0005 x y) 0)))
  have freshness2 : nb055AlphaDummy004 ≠ nb055AlphaDummy001 :=
    by
    unfold nb055AlphaDummy004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0002) 0)))
  have freshness3 : (nb055AlphaDummy005 x y) ≠ y :=
    by
    unfold nb055AlphaDummy005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0003 x y) 0)))
  have freshness4 : nb055AlphaDummy004 ≠ nb055AlphaDummy000 :=
    by
    unfold nb055AlphaDummy004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0000) 0)))
  have freshness5 : (nb055AlphaDummy005 x y) ≠ x :=
    by
    unfold nb055AlphaDummy005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0001 x y) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3
            (TAlphaVar.there freshness4 freshness5 (TAlphaVar.here _ _ _)))))

/-- Checked nominal proof certificate identified upstream as `nb055_compose_root_occurrence_0`. -/
@[expose]
noncomputable def nb055ComposeRootOccurrence0 (x y : Var) (dv_x_y : x ≠ y) :
    TAlphaClass
      [(nb055AlphaDummy002, (nb055AlphaDummy003 x y)), (nb055AlphaDummy001, y),
        (nb055AlphaDummy000, x), (nb055AlphaDummy004, (nb055AlphaDummy005 x y))]
      (Class.cv nb055AlphaDummy000) (Class.cv x) :=
  by
  have freshness0 : nb055AlphaDummy000 ≠ nb055AlphaDummy002 :=
    by
    unfold nb055AlphaDummy002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0006) 0))
  have freshness1 : x ≠ (nb055AlphaDummy003 x y) :=
    by
    unfold nb055AlphaDummy003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0007 x y) 0))
  have freshness2 : nb055AlphaDummy000 ≠ nb055AlphaDummy001 :=
    by
    unfold nb055AlphaDummy000 nb055AlphaDummy001
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness3 : x ≠ y := by exact dv_x_y
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

/-- Checked nominal proof certificate identified upstream as `nb055_compose_root_occurrence_1`. -/
@[expose]
noncomputable def nb055_compose_root_occurrence_1 (x y : Var) :
    TAlphaClass
      [(nb055AlphaDummy002, (nb055AlphaDummy003 x y)), (nb055AlphaDummy001, y),
        (nb055AlphaDummy000, x), (nb055AlphaDummy004, (nb055AlphaDummy005 x y))]
      (Class.cv nb055AlphaDummy001) (Class.cv y) :=
  by
  have freshness0 : nb055AlphaDummy001 ≠ nb055AlphaDummy002 :=
    by
    unfold nb055AlphaDummy002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0042) 0))
  have freshness1 : y ≠ (nb055AlphaDummy003 x y) :=
    by
    unfold nb055AlphaDummy003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0043 x y) 0))
  with_reducible
    exact (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1 (TAlphaVar.here _ _ _)))

/-- Checked nominal proof certificate identified upstream as `nb055_compose_occurrence_3`. -/
@[expose]
noncomputable def nb055ComposeOccurrence3 (x y : Var) :
    TAlphaClass
      [(nb055AlphaDummy015, (nb055AlphaDummy017 x y)),
        (nb055AlphaDummy014, (nb055AlphaDummy016 x y)),
        (nb055AlphaDummy080, (nb055AlphaDummy081 x y)),
        (nb055AlphaDummy002, (nb055AlphaDummy003 x y)), (nb055AlphaDummy001, y),
        (nb055AlphaDummy000, x), (nb055AlphaDummy004, (nb055AlphaDummy005 x y))]
      (Class.cv nb055AlphaDummy080) (Class.cv (nb055AlphaDummy081 x y)) :=
  by
  have freshness0 : nb055AlphaDummy080 ≠ nb055AlphaDummy015 :=
    by
    unfold nb055AlphaDummy080
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0094) 0)))
  have freshness1 : (nb055AlphaDummy081 x y) ≠ (nb055AlphaDummy017 x y) :=
    by
    unfold nb055AlphaDummy081
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0095 x y) 0)))
  have freshness2 : nb055AlphaDummy080 ≠ nb055AlphaDummy014 :=
    by
    unfold nb055AlphaDummy080
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0092) 0)))
  have freshness3 : (nb055AlphaDummy081 x y) ≠ (nb055AlphaDummy016 x y) :=
    by
    unfold nb055AlphaDummy081
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0093 x y) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

/-- Checked nominal proof certificate identified upstream as `nb055_split_alpha_0026`. -/
@[expose]
noncomputable def nb055SplitAlpha0026 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
        ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
        ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
      (Wff.imp (Wff.classEq (Class.cv (nb055AlphaDummy004)) (synCop
            (synCop (Class.cv (nb055AlphaDummy000)) (Class.cv (nb055AlphaDummy001)))
            (Class.cv (nb055AlphaDummy002)))) (Wff.neg (synWa
            (synWa (Wff.classMem (Class.cv (nb055AlphaDummy000)) (synCvv))
              (Wff.classMem (Class.cv (nb055AlphaDummy001)) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy002))
              (synCcom (Class.cv (nb055AlphaDummy000))
                (Class.cv (nb055AlphaDummy001)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb055AlphaDummy005 x y))
          (synCop (synCop (Class.cv x) (Class.cv y)) (Class.cv (nb055AlphaDummy003 x y))))
        (Wff.neg (synWa (synWa (Wff.classMem (Class.cv x) (synCvv))
              (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb055AlphaDummy003 x y))
              (synCcom (Class.cv x) (Class.cv y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (nb055_compose_occurrence_2 x y) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb055SplitAlpha0009 x y dv_x_y))))) (TAlphaWff.neg
      (TAlphaWff.conj (TAlphaWff.conj
          (TAlphaWff.classMem (nb055ComposeRootOccurrence0 x y dv_x_y)
            (TAlphaClass.reflOfClosed [((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
              (synCvv) (by simp only [fv_syn_cvv])))
          (TAlphaWff.classMem (nb055_compose_root_occurrence_1 x y) (TAlphaClass.reflOfClosed
              [((nb055AlphaDummy002), (nb055AlphaDummy003 x y)),
                ((nb055AlphaDummy001), y), ((nb055AlphaDummy000), x),
                ((nb055AlphaDummy004), (nb055AlphaDummy005 x y))]
              (synCvv) (by simp only [fv_syn_cvv]))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classEq (nb055ComposeOccurrence3 x y) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0096) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0098 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0098 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0101 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0097) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0099 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb055SplitAlpha0011 x y))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0096) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0098 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0098 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0101 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0097) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0099 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb055AlphaDummy000))).fv ∪ ((Class.cv (nb055AlphaDummy001))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb055SplitAlpha0011 x y)))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb055SplitAlpha0014 x y)))))))))
                  (TAlphaWff.ex (TAlphaWff.neg (nb055SplitAlpha0025 x y dv_x_y)))))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_compose`. -/
@[expose]
noncomputable def nominalDfCompose (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCcompose)
        (synCmpt2 x (synCvv) y (synCvv) (synCcom (.cv x) (.cv y)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.ex (TAlphaWff.neg (nb055SplitAlpha0026 x y dv_x_y))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
