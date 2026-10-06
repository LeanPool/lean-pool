/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.SingletonImageAlpha


/-! NF weak partition development: NominalAlphaRepairedBase001043SiReflected001. -/


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

/-! Shared variable, support, and alpha-certificate components. -/


namespace SingletonImageAlpha

/-- Proof-translation construction identified upstream as `split_alpha_0000`. -/
@[expose]
noncomputable def splitAlpha0000 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alphaDummy022 A), (alphaDummy025 x y)),
        ((alphaDummy021 A), (alphaDummy024 x y)),
        ((alphaDummy020 A), (alphaDummy023 x y)),
        ((alphaDummy018 A), (alphaDummy019 x y)),
        ((alphaDummy014 A), (alphaDummy016 x y)),
        ((alphaDummy015 A), (alphaDummy017 x y)),
        ((alphaDummy007 A), (alphaDummy009 x y)),
        ((alphaDummy006 A), (alphaDummy008 x y)),
        ((alphaDummy012 A), (alphaDummy013 x y)),
        ((alphaDummy010 A), (alphaDummy011 x y)), ((alphaDummy002 A), y),
        ((alphaDummy001 A), x), ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy021 A)) (Class.cv (alphaDummy022 A))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy020 A))
            (synCun (Class.cv (alphaDummy021 A)) (Class.cv (alphaDummy022 A))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy023 x y))
            (synCun (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy022 A), (alphaDummy025 x y)),
          ((alphaDummy021 A), (alphaDummy024 x y)),
          ((alphaDummy020 A), (alphaDummy023 x y)),
          ((alphaDummy018 A), (alphaDummy019 x y)),
          ((alphaDummy014 A), (alphaDummy016 x y)),
          ((alphaDummy015 A), (alphaDummy017 x y)),
          ((alphaDummy007 A), (alphaDummy009 x y)),
          ((alphaDummy006 A), (alphaDummy008 x y)),
          ((alphaDummy012 A), (alphaDummy013 x y)),
          ((alphaDummy010 A), (alphaDummy011 x y)), ((alphaDummy002 A), y),
          ((alphaDummy001 A), x), ((alphaDummy004 A), (alphaDummy005 x y z w A))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0001`. -/
@[expose]
noncomputable def splitAlpha0001 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((alphaDummy007 A), (alphaDummy009 x y)),
        ((alphaDummy006 A), (alphaDummy008 x y)),
        ((alphaDummy012 A), (alphaDummy013 x y)),
        ((alphaDummy010 A), (alphaDummy011 x y)), ((alphaDummy002 A), y),
        ((alphaDummy001 A), x), ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy007 A)) (Class.cv (alphaDummy001 A)))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy006 A))
            (synCphi (Class.cv (alphaDummy007 A))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy009 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy008 x y))
            (synCphi (Class.cv (alphaDummy009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0008 A) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0009 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0005 A) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0007 x y) 0))
                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (alphaDummy001 A))).fv ∪ ((Class.cv (alphaDummy002 A))).fv)
              (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (alphaDummy007 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy009 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((alphaDummy022 A), (alphaDummy025 x y)),
        ((alphaDummy021 A), (alphaDummy024 x y)),
        ((alphaDummy020 A), (alphaDummy023 x y)),
        ((alphaDummy018 A), (alphaDummy019 x y)),
        ((alphaDummy014 A), (alphaDummy016 x y)),
        ((alphaDummy015 A), (alphaDummy017 x y)),
        ((alphaDummy007 A), (alphaDummy009 x y)),
        ((alphaDummy006 A), (alphaDummy008 x y)),
        ((alphaDummy012 A), (alphaDummy013 x y)),
        ((alphaDummy010 A), (alphaDummy011 x y)), ((alphaDummy002 A), y),
        ((alphaDummy001 A), x), ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0000 x y z w A))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy018 A), (alphaDummy019 x y)),
                              ((alphaDummy014 A), (alphaDummy016 x y)),
                              ((alphaDummy015 A), (alphaDummy017 x y)),
                              ((alphaDummy007 A), (alphaDummy009 x y)),
                              ((alphaDummy006 A), (alphaDummy008 x y)),
                              ((alphaDummy012 A), (alphaDummy013 x y)),
                              ((alphaDummy010 A), (alphaDummy011 x y)),
                              ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                              ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy018 A), (alphaDummy019 x y)),
                              ((alphaDummy014 A), (alphaDummy016 x y)),
                              ((alphaDummy015 A), (alphaDummy017 x y)),
                              ((alphaDummy007 A), (alphaDummy009 x y)),
                              ((alphaDummy006 A), (alphaDummy008 x y)),
                              ((alphaDummy012 A), (alphaDummy013 x y)),
                              ((alphaDummy010 A), (alphaDummy011 x y)),
                              ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                              ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0002`. -/
@[expose]
noncomputable def splitAlpha0002 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alphaDummy022 A), (alphaDummy025 x y)),
        ((alphaDummy021 A), (alphaDummy024 x y)),
        ((alphaDummy020 A), (alphaDummy023 x y)),
        ((alphaDummy018 A), (alphaDummy019 x y)),
        ((alphaDummy014 A), (alphaDummy016 x y)),
        ((alphaDummy015 A), (alphaDummy017 x y)),
        ((alphaDummy040 A), (alphaDummy041 x y)),
        ((alphaDummy038 A), (alphaDummy039 x y)),
        ((alphaDummy007 A), (alphaDummy009 x y)),
        ((alphaDummy006 A), (alphaDummy008 x y)),
        ((alphaDummy036 A), (alphaDummy037 x y)),
        ((alphaDummy010 A), (alphaDummy011 x y)), ((alphaDummy002 A), y),
        ((alphaDummy001 A), x), ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy021 A)) (Class.cv (alphaDummy022 A))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy020 A))
            (synCun (Class.cv (alphaDummy021 A)) (Class.cv (alphaDummy022 A))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy023 x y))
            (synCun (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy022 A), (alphaDummy025 x y)),
          ((alphaDummy021 A), (alphaDummy024 x y)),
          ((alphaDummy020 A), (alphaDummy023 x y)),
          ((alphaDummy018 A), (alphaDummy019 x y)),
          ((alphaDummy014 A), (alphaDummy016 x y)),
          ((alphaDummy015 A), (alphaDummy017 x y)),
          ((alphaDummy040 A), (alphaDummy041 x y)),
          ((alphaDummy038 A), (alphaDummy039 x y)),
          ((alphaDummy007 A), (alphaDummy009 x y)),
          ((alphaDummy006 A), (alphaDummy008 x y)),
          ((alphaDummy036 A), (alphaDummy037 x y)),
          ((alphaDummy010 A), (alphaDummy011 x y)), ((alphaDummy002 A), y),
          ((alphaDummy001 A), x), ((alphaDummy004 A), (alphaDummy005 x y z w A))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy014 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0003`. -/
@[expose]
noncomputable def splitAlpha0003 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alphaDummy040 A), (alphaDummy041 x y)),
        ((alphaDummy038 A), (alphaDummy039 x y)),
        ((alphaDummy007 A), (alphaDummy009 x y)),
        ((alphaDummy006 A), (alphaDummy008 x y)),
        ((alphaDummy036 A), (alphaDummy037 x y)),
        ((alphaDummy010 A), (alphaDummy011 x y)), ((alphaDummy002 A), y),
        ((alphaDummy001 A), x), ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy040 A))
          (synCphi (Class.cv (alphaDummy007 A)))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy040 A))
            (synCphi (Class.cv (alphaDummy007 A))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy041 x y))
          (synCphi (Class.cv (alphaDummy009 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy041 x y))
            (synCphi (Class.cv (alphaDummy009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0040 A) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0)) (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0038 A) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (alphaDummy007 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (alphaDummy009 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0014 A) 1)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0015 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A) 0)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0015 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((alphaDummy022 A), (alphaDummy025 x y)),
                                        ((alphaDummy021 A), (alphaDummy024 x y)),
                                        ((alphaDummy020 A), (alphaDummy023 x y)),
                                        ((alphaDummy018 A), (alphaDummy019 x y)),
                                        ((alphaDummy014 A), (alphaDummy016 x y)),
                                        ((alphaDummy015 A), (alphaDummy017 x y)),
                                        ((alphaDummy040 A), (alphaDummy041 x y)),
                                        ((alphaDummy038 A), (alphaDummy039 x y)),
                                        ((alphaDummy007 A), (alphaDummy009 x y)),
                                        ((alphaDummy006 A), (alphaDummy008 x y)),
                                        ((alphaDummy036 A), (alphaDummy037 x y)),
                                        ((alphaDummy010 A), (alphaDummy011 x y)),
                                        ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                                        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                      (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (splitAlpha0002 x y z w A))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((alphaDummy018 A), (alphaDummy019 x y)),
                            ((alphaDummy014 A), (alphaDummy016 x y)),
                            ((alphaDummy015 A), (alphaDummy017 x y)),
                            ((alphaDummy040 A), (alphaDummy041 x y)),
                            ((alphaDummy038 A), (alphaDummy039 x y)),
                            ((alphaDummy007 A), (alphaDummy009 x y)),
                            ((alphaDummy006 A), (alphaDummy008 x y)),
                            ((alphaDummy036 A), (alphaDummy037 x y)),
                            ((alphaDummy010 A), (alphaDummy011 x y)),
                            ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                            ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((alphaDummy018 A), (alphaDummy019 x y)),
                            ((alphaDummy014 A), (alphaDummy016 x y)),
                            ((alphaDummy015 A), (alphaDummy017 x y)),
                            ((alphaDummy040 A), (alphaDummy041 x y)),
                            ((alphaDummy038 A), (alphaDummy039 x y)),
                            ((alphaDummy007 A), (alphaDummy009 x y)),
                            ((alphaDummy006 A), (alphaDummy008 x y)),
                            ((alphaDummy036 A), (alphaDummy037 x y)),
                            ((alphaDummy010 A), (alphaDummy011 x y)),
                            ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                            ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1)) (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0040 A) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0))
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0038 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (alphaDummy007 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy009 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((alphaDummy022 A), (alphaDummy025 x y)),
        ((alphaDummy021 A), (alphaDummy024 x y)),
        ((alphaDummy020 A), (alphaDummy023 x y)),
        ((alphaDummy018 A), (alphaDummy019 x y)),
        ((alphaDummy014 A), (alphaDummy016 x y)),
        ((alphaDummy015 A), (alphaDummy017 x y)),
        ((alphaDummy040 A), (alphaDummy041 x y)),
        ((alphaDummy038 A), (alphaDummy039 x y)),
        ((alphaDummy007 A), (alphaDummy009 x y)),
        ((alphaDummy006 A), (alphaDummy008 x y)),
        ((alphaDummy036 A), (alphaDummy037 x y)),
        ((alphaDummy010 A), (alphaDummy011 x y)), ((alphaDummy002 A), y),
        ((alphaDummy001 A), x), ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0002 x y z w A))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy018 A), (alphaDummy019 x y)),
                              ((alphaDummy014 A), (alphaDummy016 x y)),
                              ((alphaDummy015 A), (alphaDummy017 x y)),
                              ((alphaDummy040 A), (alphaDummy041 x y)),
                              ((alphaDummy038 A), (alphaDummy039 x y)),
                              ((alphaDummy007 A), (alphaDummy009 x y)),
                              ((alphaDummy006 A), (alphaDummy008 x y)),
                              ((alphaDummy036 A), (alphaDummy037 x y)),
                              ((alphaDummy010 A), (alphaDummy011 x y)),
                              ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                              ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy018 A), (alphaDummy019 x y)),
                              ((alphaDummy014 A), (alphaDummy016 x y)),
                              ((alphaDummy015 A), (alphaDummy017 x y)),
                              ((alphaDummy040 A), (alphaDummy041 x y)),
                              ((alphaDummy038 A), (alphaDummy039 x y)),
                              ((alphaDummy007 A), (alphaDummy009 x y)),
                              ((alphaDummy006 A), (alphaDummy008 x y)),
                              ((alphaDummy036 A), (alphaDummy037 x y)),
                              ((alphaDummy010 A), (alphaDummy011 x y)),
                              ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                              ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `swapped_variable`. -/
@[expose]
def swappedVariable (x y z w : Var) (A : Class) :
    TAlphaClass
      [((alphaDummy002 A), y), ((alphaDummy001 A), x),
        ((alphaDummy004 A), alphaDummy005 x y z w A)]
      (Class.cv (alphaDummy004 A)) (Class.cv (alphaDummy005 x y z w A)) :=
  by
  have leftSecond : (alphaDummy002 A) ≠ (alphaDummy004 A) :=
    by
    unfold alphaDummy004
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0002 A) 0)
  have rightSecond : y ≠ alphaDummy005 x y z w A :=
    by
    unfold alphaDummy005
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0003 x y z w A) 0)
  have leftFirst : (alphaDummy001 A) ≠ (alphaDummy004 A) :=
    by
    unfold alphaDummy004
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0000 A) 0)
  have rightFirst : x ≠ alphaDummy005 x y z w A :=
    by
    unfold alphaDummy005
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0001 x y z w A) 0)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there leftSecond.symm rightSecond.symm
          (TAlphaVar.there leftFirst.symm rightFirst.symm (TAlphaVar.here _ _ _))))

/-- Proof-translation construction identified upstream as `split_alpha_0004`. -/
@[expose]
noncomputable def splitAlpha0004 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((alphaDummy002 A), y), ((alphaDummy001 A), x),
        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.classEq (Class.cv (alphaDummy004 A))
        (synCop (Class.cv (alphaDummy001 A)) (Class.cv (alphaDummy002 A))))
      (Wff.classEq (Class.cv (alphaDummy005 x y z w A))
        (synCop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (swappedVariable x y z w A) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0001 x y z w A dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0001 x y z w A dv_x_y)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0036 A) 0)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0033 A) 0)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy001 A))).fv ∪
                                    ((Class.cv (alphaDummy002 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (splitAlpha0003 x y z w A)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((alphaDummy038 A), (alphaDummy039 x y)),
                                        ((alphaDummy007 A), (alphaDummy009 x y)),
                                        ((alphaDummy006 A), (alphaDummy008 x y)),
                                        ((alphaDummy036 A), (alphaDummy037 x y)),
                                        ((alphaDummy010 A), (alphaDummy011 x y)),
                                        ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                                        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                      (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0036 A) 0)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0033 A) 0)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy001 A))).fv ∪
                                    ((Class.cv (alphaDummy002 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (splitAlpha0003 x y z w A)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((alphaDummy038 A), (alphaDummy039 x y)),
                                        ((alphaDummy007 A), (alphaDummy009 x y)),
                                        ((alphaDummy006 A), (alphaDummy008 x y)),
                                        ((alphaDummy036 A), (alphaDummy037 x y)),
                                        ((alphaDummy010 A), (alphaDummy011 x y)),
                                        ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                                        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                      (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0005`. -/
@[expose]
noncomputable def splitAlpha0005 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alphaDummy062 A), (alphaDummy065 z w)),
        ((alphaDummy061 A), (alphaDummy064 z w)),
        ((alphaDummy060 A), (alphaDummy063 z w)),
        ((alphaDummy058 A), (alphaDummy059 z w)),
        ((alphaDummy054 A), (alphaDummy056 z w)),
        ((alphaDummy055 A), (alphaDummy057 z w)),
        ((alphaDummy047 A), (alphaDummy049 z w)),
        ((alphaDummy046 A), (alphaDummy048 z w)),
        ((alphaDummy052 A), (alphaDummy053 z w)),
        ((alphaDummy050 A), (alphaDummy051 z w)), ((alphaDummy000 A), w),
        ((alphaDummy003 A), z), ((alphaDummy002 A), y), ((alphaDummy001 A), x),
        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy061 A)) (Class.cv (alphaDummy062 A))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy060 A))
            (synCun (Class.cv (alphaDummy061 A)) (Class.cv (alphaDummy062 A))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy064 z w)) (Class.cv (alphaDummy065 z w))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy063 z w))
            (synCun (Class.cv (alphaDummy064 z w)) (Class.cv (alphaDummy065 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy062 A), (alphaDummy065 z w)),
          ((alphaDummy061 A), (alphaDummy064 z w)),
          ((alphaDummy060 A), (alphaDummy063 z w)),
          ((alphaDummy058 A), (alphaDummy059 z w)),
          ((alphaDummy054 A), (alphaDummy056 z w)),
          ((alphaDummy055 A), (alphaDummy057 z w)),
          ((alphaDummy047 A), (alphaDummy049 z w)),
          ((alphaDummy046 A), (alphaDummy048 z w)),
          ((alphaDummy052 A), (alphaDummy053 z w)),
          ((alphaDummy050 A), (alphaDummy051 z w)), ((alphaDummy000 A), w),
          ((alphaDummy003 A), z), ((alphaDummy002 A), y), ((alphaDummy001 A), x),
          ((alphaDummy004 A), (alphaDummy005 x y z w A))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0071 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0071 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0006`. -/
@[expose]
noncomputable def splitAlpha0006 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [((alphaDummy047 A), (alphaDummy049 z w)),
        ((alphaDummy046 A), (alphaDummy048 z w)),
        ((alphaDummy052 A), (alphaDummy053 z w)),
        ((alphaDummy050 A), (alphaDummy051 z w)), ((alphaDummy000 A), w),
        ((alphaDummy003 A), z), ((alphaDummy002 A), y), ((alphaDummy001 A), x),
        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy047 A)) (Class.cv (alphaDummy003 A)))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy046 A))
            (synCphi (Class.cv (alphaDummy047 A))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy049 z w)) (Class.cv z)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy048 z w))
            (synCphi (Class.cv (alphaDummy049 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 z w) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 z w) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0047 A) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 0))
                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                  (Ne.symm dv_w_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (alphaDummy003 A))).fv ∪ ((Class.cv (alphaDummy000 A))).fv)
              (by decide))
            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (alphaDummy047 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy049 z w))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0056 A) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0057 z w) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0056 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0057 z w) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0054 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0055 z w) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((alphaDummy062 A), (alphaDummy065 z w)),
        ((alphaDummy061 A), (alphaDummy064 z w)),
        ((alphaDummy060 A), (alphaDummy063 z w)),
        ((alphaDummy058 A), (alphaDummy059 z w)),
        ((alphaDummy054 A), (alphaDummy056 z w)),
        ((alphaDummy055 A), (alphaDummy057 z w)),
        ((alphaDummy047 A), (alphaDummy049 z w)),
        ((alphaDummy046 A), (alphaDummy048 z w)),
        ((alphaDummy052 A), (alphaDummy053 z w)),
        ((alphaDummy050 A), (alphaDummy051 z w)), ((alphaDummy000 A), w),
        ((alphaDummy003 A), z), ((alphaDummy002 A), y), ((alphaDummy001 A), x),
        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0005 x y z w A))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy058 A), (alphaDummy059 z w)),
                              ((alphaDummy054 A), (alphaDummy056 z w)),
                              ((alphaDummy055 A), (alphaDummy057 z w)),
                              ((alphaDummy047 A), (alphaDummy049 z w)),
                              ((alphaDummy046 A), (alphaDummy048 z w)),
                              ((alphaDummy052 A), (alphaDummy053 z w)),
                              ((alphaDummy050 A), (alphaDummy051 z w)),
                              ((alphaDummy000 A), w), ((alphaDummy003 A), z),
                              ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                              ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy058 A), (alphaDummy059 z w)),
                              ((alphaDummy054 A), (alphaDummy056 z w)),
                              ((alphaDummy055 A), (alphaDummy057 z w)),
                              ((alphaDummy047 A), (alphaDummy049 z w)),
                              ((alphaDummy046 A), (alphaDummy048 z w)),
                              ((alphaDummy052 A), (alphaDummy053 z w)),
                              ((alphaDummy050 A), (alphaDummy051 z w)),
                              ((alphaDummy000 A), w), ((alphaDummy003 A), z),
                              ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                              ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0007`. -/
@[expose]
noncomputable def splitAlpha0007 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alphaDummy062 A), (alphaDummy065 z w)),
        ((alphaDummy061 A), (alphaDummy064 z w)),
        ((alphaDummy060 A), (alphaDummy063 z w)),
        ((alphaDummy058 A), (alphaDummy059 z w)),
        ((alphaDummy054 A), (alphaDummy056 z w)),
        ((alphaDummy055 A), (alphaDummy057 z w)),
        ((alphaDummy080 A), (alphaDummy081 z w)),
        ((alphaDummy078 A), (alphaDummy079 z w)),
        ((alphaDummy047 A), (alphaDummy049 z w)),
        ((alphaDummy046 A), (alphaDummy048 z w)),
        ((alphaDummy076 A), (alphaDummy077 z w)),
        ((alphaDummy050 A), (alphaDummy051 z w)), ((alphaDummy000 A), w),
        ((alphaDummy003 A), z), ((alphaDummy002 A), y), ((alphaDummy001 A), x),
        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy061 A)) (Class.cv (alphaDummy062 A))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy060 A))
            (synCun (Class.cv (alphaDummy061 A)) (Class.cv (alphaDummy062 A))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy064 z w)) (Class.cv (alphaDummy065 z w))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy063 z w))
            (synCun (Class.cv (alphaDummy064 z w)) (Class.cv (alphaDummy065 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy062 A), (alphaDummy065 z w)),
          ((alphaDummy061 A), (alphaDummy064 z w)),
          ((alphaDummy060 A), (alphaDummy063 z w)),
          ((alphaDummy058 A), (alphaDummy059 z w)),
          ((alphaDummy054 A), (alphaDummy056 z w)),
          ((alphaDummy055 A), (alphaDummy057 z w)),
          ((alphaDummy080 A), (alphaDummy081 z w)),
          ((alphaDummy078 A), (alphaDummy079 z w)),
          ((alphaDummy047 A), (alphaDummy049 z w)),
          ((alphaDummy046 A), (alphaDummy048 z w)),
          ((alphaDummy076 A), (alphaDummy077 z w)),
          ((alphaDummy050 A), (alphaDummy051 z w)), ((alphaDummy000 A), w),
          ((alphaDummy003 A), z), ((alphaDummy002 A), y), ((alphaDummy001 A), x),
          ((alphaDummy004 A), (alphaDummy005 x y z w A))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy054 A))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy056 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0071 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0071 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0008`. -/
@[expose]
noncomputable def splitAlpha0008 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alphaDummy055 A), (alphaDummy057 z w)),
        ((alphaDummy080 A), (alphaDummy081 z w)),
        ((alphaDummy078 A), (alphaDummy079 z w)),
        ((alphaDummy047 A), (alphaDummy049 z w)),
        ((alphaDummy046 A), (alphaDummy048 z w)),
        ((alphaDummy076 A), (alphaDummy077 z w)),
        ((alphaDummy050 A), (alphaDummy051 z w)), ((alphaDummy000 A), w),
        ((alphaDummy003 A), z), ((alphaDummy002 A), y), ((alphaDummy001 A), x),
        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.all (alphaDummy054 A) (Wff.neg (synWa
            (Wff.classMem (Class.cv (alphaDummy054 A)) (Class.cv (alphaDummy047 A)))
            (Wff.classEq (Class.cv (alphaDummy055 A))
              (synCif (Wff.classMem (Class.cv (alphaDummy054 A)) (synCnnc))
                (synCplc (Class.cv (alphaDummy054 A)) (synC1c))
                (Class.cv (alphaDummy054 A)))))))
      (Wff.all (alphaDummy056 z w) (Wff.neg (synWa
            (Wff.classMem (Class.cv (alphaDummy056 z w)) (Class.cv (alphaDummy049 z w)))
            (Wff.classEq (Class.cv (alphaDummy057 z w))
              (synCif (Wff.classMem (Class.cv (alphaDummy056 z w)) (synCnnc))
                (synCplc (Class.cv (alphaDummy056 z w)) (synC1c))
                (Class.cv (alphaDummy056 z w))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 A) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0083 z w) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0081 z w) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy047 A))).fv) (by decide))
              (freshVar_injective (((Class.cv (alphaDummy049 z w))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0054 A) 0)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0055 z w) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((alphaDummy062 A), (alphaDummy065 z w)),
                                    ((alphaDummy061 A), (alphaDummy064 z w)),
                                    ((alphaDummy060 A), (alphaDummy063 z w)),
                                    ((alphaDummy058 A), (alphaDummy059 z w)),
                                    ((alphaDummy054 A), (alphaDummy056 z w)),
                                    ((alphaDummy055 A), (alphaDummy057 z w)),
                                    ((alphaDummy080 A), (alphaDummy081 z w)),
                                    ((alphaDummy078 A), (alphaDummy079 z w)),
                                    ((alphaDummy047 A), (alphaDummy049 z w)),
                                    ((alphaDummy046 A), (alphaDummy048 z w)),
                                    ((alphaDummy076 A), (alphaDummy077 z w)),
                                    ((alphaDummy050 A), (alphaDummy051 z w)),
                                    ((alphaDummy000 A), w), ((alphaDummy003 A), z),
                                    ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                                    ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                  (synC1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (splitAlpha0007 x y z w A))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((alphaDummy058 A), (alphaDummy059 z w)),
                        ((alphaDummy054 A), (alphaDummy056 z w)),
                        ((alphaDummy055 A), (alphaDummy057 z w)),
                        ((alphaDummy080 A), (alphaDummy081 z w)),
                        ((alphaDummy078 A), (alphaDummy079 z w)),
                        ((alphaDummy047 A), (alphaDummy049 z w)),
                        ((alphaDummy046 A), (alphaDummy048 z w)),
                        ((alphaDummy076 A), (alphaDummy077 z w)),
                        ((alphaDummy050 A), (alphaDummy051 z w)),
                        ((alphaDummy000 A), w), ((alphaDummy003 A), z),
                        ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                      (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((alphaDummy058 A), (alphaDummy059 z w)),
                        ((alphaDummy054 A), (alphaDummy056 z w)),
                        ((alphaDummy055 A), (alphaDummy057 z w)),
                        ((alphaDummy080 A), (alphaDummy081 z w)),
                        ((alphaDummy078 A), (alphaDummy079 z w)),
                        ((alphaDummy047 A), (alphaDummy049 z w)),
                        ((alphaDummy046 A), (alphaDummy048 z w)),
                        ((alphaDummy076 A), (alphaDummy077 z w)),
                        ((alphaDummy050 A), (alphaDummy051 z w)),
                        ((alphaDummy000 A), w), ((alphaDummy003 A), z),
                        ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                      (synCnnc) (by simp only [fv_syn_cnnc])))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0009`. -/
@[expose]
noncomputable def splitAlpha0009 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [((alphaDummy050 A), (alphaDummy051 z w)), ((alphaDummy000 A), w),
        ((alphaDummy003 A), z), ((alphaDummy002 A), y), ((alphaDummy001 A), x),
        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy050 A)) (synCcompl
            (Class.cab (alphaDummy046 A)
              (synWrex (alphaDummy047 A) (Class.cv (alphaDummy003 A))
                (Wff.classEq (Class.cv (alphaDummy046 A))
                  (synCphi (Class.cv (alphaDummy047 A)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy050 A)) (synCcompl
              (Class.cab (alphaDummy046 A)
                (synWrex (alphaDummy047 A) (Class.cv (alphaDummy000 A))
                  (Wff.classEq (Class.cv (alphaDummy046 A))
                    (synCun (synCphi (Class.cv (alphaDummy047 A)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy051 z w)) (synCcompl
            (Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy048 z w))
                  (synCphi (Class.cv (alphaDummy049 z w)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy051 z w)) (synCcompl
              (Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv w)
                  (Wff.classEq (Class.cv (alphaDummy048 z w))
                    (synCun (synCphi (Class.cv (alphaDummy049 z w)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0006 x y z w A dv_w_z)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0006 x y z w A dv_w_z)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0078 A) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alphaDummy003 A))).fv ∪
                                ((Class.cv (alphaDummy000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w A)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w A))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((alphaDummy078 A), (alphaDummy079 z w)),
                                    ((alphaDummy047 A), (alphaDummy049 z w)),
                                    ((alphaDummy046 A), (alphaDummy048 z w)),
                                    ((alphaDummy076 A), (alphaDummy077 z w)),
                                    ((alphaDummy050 A), (alphaDummy051 z w)),
                                    ((alphaDummy000 A), w), ((alphaDummy003 A), z),
                                    ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                                    ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0078 A) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alphaDummy003 A))).fv ∪
                                ((Class.cv (alphaDummy000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w A)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w A))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((alphaDummy078 A), (alphaDummy079 z w)),
                                    ((alphaDummy047 A), (alphaDummy049 z w)),
                                    ((alphaDummy046 A), (alphaDummy048 z w)),
                                    ((alphaDummy076 A), (alphaDummy077 z w)),
                                    ((alphaDummy050 A), (alphaDummy051 z w)),
                                    ((alphaDummy000 A), w), ((alphaDummy003 A), z),
                                    ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                                    ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

/-- Proof-translation construction identified upstream as `wpp_refl_0014`. -/
@[expose]
noncomputable def wppRefl0014 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) :
    TReflOn
      [((alphaDummy000 A), w), ((alphaDummy003 A), z), ((alphaDummy002 A), y),
        ((alphaDummy001 A), x), ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (A).fv :=
  by
  intro u hu
  exact
    (TAlphaVar.there (fun h_eq => ((wpp_notmem_0212 A)) (h_eq ▸ hu))
      (fun h_eq => ((wpp_notmem_0213 w A dv_A_w)) (h_eq ▸ hu))
      (TAlphaVar.there (fun h_eq => ((wpp_notmem_0210 A)) (h_eq ▸ hu))
        (fun h_eq => ((wpp_notmem_0211 z A dv_A_z)) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => ((wpp_notmem_0208 A)) (h_eq ▸ hu))
          (fun h_eq => ((wpp_notmem_0209 y A dv_A_y)) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => ((wpp_notmem_0206 A)) (h_eq ▸ hu))
            (fun h_eq => ((wpp_notmem_0207 x A dv_A_x)) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => ((wpp_notmem_0204 A)) (h_eq ▸ hu))
              (fun h_eq => ((wpp_notmem_0205 x y z w A dv_A_w dv_A_z)) (h_eq ▸ hu))
              (TAlphaVar.free (by simp) (by simp)))))))

end SingletonImageAlpha

/-- Checked nominal proof certificate identified upstream as `nominal_df_si`. -/
@[expose]
noncomputable def nominalDfSi (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCsi A) (synCopab x y (synWex z (synWex w
              (synW3a (.classEq (.cv x) (synCsn (.cv z)))
                (.classEq (.cv y) (synCsn (.cv w))) (synWbr (.cv z) A (.cv w))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (SingletonImageAlpha.splitAlpha0004 x y z w A dv_x_y)
              (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.classEq
                        (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                            (Ne.symm dv_w_x)
                            (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_z
                              (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                dv_x_y (TAlphaVar.here _ _ _))))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
                                    (SingletonImageAlpha.support_mem_0042 A) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (SingletonImageAlpha.support_mem_0043 z) 0))
                                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                  (Ne.symm dv_w_z) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                            (Ne.symm dv_w_y)
                            (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                              dv_y_z (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
                                    (SingletonImageAlpha.support_mem_0044 A) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (SingletonImageAlpha.support_mem_0045 w) 0))
                                (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                            (SingletonImageAlpha.splitAlpha0009 x y z w A dv_w_z))))
                      (TAlphaClass.reflOfReflOn [((SingletonImageAlpha.alphaDummy000 A), w),
                          ((SingletonImageAlpha.alphaDummy003 A), z),
                          ((SingletonImageAlpha.alphaDummy002 A), y),
                          ((SingletonImageAlpha.alphaDummy001 A), x),
                          ((SingletonImageAlpha.alphaDummy004 A),
                            (SingletonImageAlpha.alphaDummy005 x y z w A))] A
                        (SingletonImageAlpha.wppRefl0014 x y z w A dv_A_w dv_A_x dv_A_y
                          dv_A_z))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
