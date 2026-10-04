/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.SwapAlpha


/-! NF weak partition development: NominalAlphaRepairedBase001039SwapReflected001. -/


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

/-! Shared variable, support, and alpha-certificate components for swap. -/


namespace SwapAlpha

/-- Proof-translation construction identified upstream as `split_alpha_0000`. -/
@[expose]
noncomputable def splitAlpha0000 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy022, (alphaDummy025 x y)), (alphaDummy021, (alphaDummy024 x y)),
        (alphaDummy020, (alphaDummy023 x y)),
        (alphaDummy018, (alphaDummy019 x y)),
        (alphaDummy014, (alphaDummy016 x y)),
        (alphaDummy015, (alphaDummy017 x y)),
        (alphaDummy007, (alphaDummy009 x y)),
        (alphaDummy006, (alphaDummy008 x y)),
        (alphaDummy012, (alphaDummy013 x y)),
        (alphaDummy010, (alphaDummy011 x y)), (alphaDummy002, y),
        (alphaDummy001, x), (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy021) (Class.cv alphaDummy022))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy020)
            (synCun (Class.cv alphaDummy021) (Class.cv alphaDummy022)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy023 x y))
            (synCun (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy022, (alphaDummy025 x y)), (alphaDummy021, (alphaDummy024 x y)),
          (alphaDummy020, (alphaDummy023 x y)), (alphaDummy018, (alphaDummy019 x y)),
          (alphaDummy014, (alphaDummy016 x y)), (alphaDummy015, (alphaDummy017 x y)),
          (alphaDummy007, (alphaDummy009 x y)), (alphaDummy006, (alphaDummy008 x y)),
          (alphaDummy012, (alphaDummy013 x y)),
          (alphaDummy010, (alphaDummy011 x y)), (alphaDummy002, y),
          (alphaDummy001, x), (alphaDummy004, (alphaDummy005 x y z w))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0001`. -/
@[expose]
noncomputable def splitAlpha0001 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [(alphaDummy007, (alphaDummy009 x y)), (alphaDummy006, (alphaDummy008 x y)),
        (alphaDummy012, (alphaDummy013 x y)),
        (alphaDummy010, (alphaDummy011 x y)), (alphaDummy002, y),
        (alphaDummy001, x), (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy007) (Class.cv alphaDummy001)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy006) (synCphi (Class.cv alphaDummy007)))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy009 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy008 x y))
            (synCphi (Class.cv (alphaDummy009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0009 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0007 x y) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy007)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy009 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy022, (alphaDummy025 x y)),
        (alphaDummy021, (alphaDummy024 x y)), (alphaDummy020, (alphaDummy023 x y)),
        (alphaDummy018, (alphaDummy019 x y)), (alphaDummy014, (alphaDummy016 x y)),
        (alphaDummy015, (alphaDummy017 x y)), (alphaDummy007, (alphaDummy009 x y)),
        (alphaDummy006, (alphaDummy008 x y)), (alphaDummy012, (alphaDummy013 x y)),
        (alphaDummy010, (alphaDummy011 x y)), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0000 x y z w))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy018, (alphaDummy019 x y)),
                              (alphaDummy014, (alphaDummy016 x y)),
                              (alphaDummy015, (alphaDummy017 x y)),
                              (alphaDummy007, (alphaDummy009 x y)),
                              (alphaDummy006, (alphaDummy008 x y)),
                              (alphaDummy012, (alphaDummy013 x y)),
                              (alphaDummy010, (alphaDummy011 x y)),
                              (alphaDummy002, y), (alphaDummy001, x),
                              (alphaDummy004, (alphaDummy005 x y z w))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy018, (alphaDummy019 x y)),
                              (alphaDummy014, (alphaDummy016 x y)),
                              (alphaDummy015, (alphaDummy017 x y)),
                              (alphaDummy007, (alphaDummy009 x y)),
                              (alphaDummy006, (alphaDummy008 x y)),
                              (alphaDummy012, (alphaDummy013 x y)),
                              (alphaDummy010, (alphaDummy011 x y)),
                              (alphaDummy002, y), (alphaDummy001, x),
                              (alphaDummy004, (alphaDummy005 x y z w))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0002`. -/
@[expose]
noncomputable def splitAlpha0002 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy022, (alphaDummy025 x y)), (alphaDummy021, (alphaDummy024 x y)),
        (alphaDummy020, (alphaDummy023 x y)),
        (alphaDummy018, (alphaDummy019 x y)),
        (alphaDummy014, (alphaDummy016 x y)),
        (alphaDummy015, (alphaDummy017 x y)),
        (alphaDummy040, (alphaDummy041 x y)),
        (alphaDummy038, (alphaDummy039 x y)),
        (alphaDummy007, (alphaDummy009 x y)),
        (alphaDummy006, (alphaDummy008 x y)),
        (alphaDummy036, (alphaDummy037 x y)),
        (alphaDummy010, (alphaDummy011 x y)), (alphaDummy002, y),
        (alphaDummy001, x), (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy021) (Class.cv alphaDummy022))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy020)
            (synCun (Class.cv alphaDummy021) (Class.cv alphaDummy022)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy023 x y))
            (synCun (Class.cv (alphaDummy024 x y)) (Class.cv (alphaDummy025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy022, (alphaDummy025 x y)), (alphaDummy021, (alphaDummy024 x y)),
          (alphaDummy020, (alphaDummy023 x y)), (alphaDummy018, (alphaDummy019 x y)),
          (alphaDummy014, (alphaDummy016 x y)), (alphaDummy015, (alphaDummy017 x y)),
          (alphaDummy040, (alphaDummy041 x y)), (alphaDummy038, (alphaDummy039 x y)),
          (alphaDummy007, (alphaDummy009 x y)), (alphaDummy006, (alphaDummy008 x y)),
          (alphaDummy036, (alphaDummy037 x y)),
          (alphaDummy010, (alphaDummy011 x y)), (alphaDummy002, y),
          (alphaDummy001, x), (alphaDummy004, (alphaDummy005 x y z w))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy016 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0003`. -/
@[expose]
noncomputable def splitAlpha0003 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy040, (alphaDummy041 x y)), (alphaDummy038, (alphaDummy039 x y)),
        (alphaDummy007, (alphaDummy009 x y)),
        (alphaDummy006, (alphaDummy008 x y)),
        (alphaDummy036, (alphaDummy037 x y)),
        (alphaDummy010, (alphaDummy011 x y)), (alphaDummy002, y),
        (alphaDummy001, x), (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy040) (synCphi (Class.cv alphaDummy007)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy040)
            (synCphi (Class.cv alphaDummy007)))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy041 x y))
          (synCphi (Class.cv (alphaDummy009 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy041 x y))
            (synCphi (Class.cv (alphaDummy009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv alphaDummy007)).fv) (by decide))
                  (freshVar_injective (((Class.cv (alphaDummy009 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [(alphaDummy022, (alphaDummy025 x y)),
                                        (alphaDummy021, (alphaDummy024 x y)),
                                        (alphaDummy020, (alphaDummy023 x y)),
                                        (alphaDummy018, (alphaDummy019 x y)),
                                        (alphaDummy014, (alphaDummy016 x y)),
                                        (alphaDummy015, (alphaDummy017 x y)),
                                        (alphaDummy040, (alphaDummy041 x y)),
                                        (alphaDummy038, (alphaDummy039 x y)),
                                        (alphaDummy007, (alphaDummy009 x y)),
                                        (alphaDummy006, (alphaDummy008 x y)),
                                        (alphaDummy036, (alphaDummy037 x y)),
                                        (alphaDummy010, (alphaDummy011 x y)),
                                        (alphaDummy002, y), (alphaDummy001, x),
                                        (alphaDummy004, (alphaDummy005 x y z w))]
                                      (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (splitAlpha0002 x y z w))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [(alphaDummy018, (alphaDummy019 x y)),
                            (alphaDummy014, (alphaDummy016 x y)),
                            (alphaDummy015, (alphaDummy017 x y)),
                            (alphaDummy040, (alphaDummy041 x y)),
                            (alphaDummy038, (alphaDummy039 x y)),
                            (alphaDummy007, (alphaDummy009 x y)),
                            (alphaDummy006, (alphaDummy008 x y)),
                            (alphaDummy036, (alphaDummy037 x y)),
                            (alphaDummy010, (alphaDummy011 x y)),
                            (alphaDummy002, y), (alphaDummy001, x),
                            (alphaDummy004, (alphaDummy005 x y z w))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [(alphaDummy018, (alphaDummy019 x y)),
                            (alphaDummy014, (alphaDummy016 x y)),
                            (alphaDummy015, (alphaDummy017 x y)),
                            (alphaDummy040, (alphaDummy041 x y)),
                            (alphaDummy038, (alphaDummy039 x y)),
                            (alphaDummy007, (alphaDummy009 x y)),
                            (alphaDummy006, (alphaDummy008 x y)),
                            (alphaDummy036, (alphaDummy037 x y)),
                            (alphaDummy010, (alphaDummy011 x y)),
                            (alphaDummy002, y), (alphaDummy001, x),
                            (alphaDummy004, (alphaDummy005 x y z w))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0))
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy007)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy009 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy022, (alphaDummy025 x y)),
        (alphaDummy021, (alphaDummy024 x y)), (alphaDummy020, (alphaDummy023 x y)),
        (alphaDummy018, (alphaDummy019 x y)), (alphaDummy014, (alphaDummy016 x y)),
        (alphaDummy015, (alphaDummy017 x y)), (alphaDummy040, (alphaDummy041 x y)),
        (alphaDummy038, (alphaDummy039 x y)), (alphaDummy007, (alphaDummy009 x y)),
        (alphaDummy006, (alphaDummy008 x y)), (alphaDummy036, (alphaDummy037 x y)),
        (alphaDummy010, (alphaDummy011 x y)), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0002 x y z w))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy018, (alphaDummy019 x y)),
                              (alphaDummy014, (alphaDummy016 x y)),
                              (alphaDummy015, (alphaDummy017 x y)),
                              (alphaDummy040, (alphaDummy041 x y)),
                              (alphaDummy038, (alphaDummy039 x y)),
                              (alphaDummy007, (alphaDummy009 x y)),
                              (alphaDummy006, (alphaDummy008 x y)),
                              (alphaDummy036, (alphaDummy037 x y)),
                              (alphaDummy010, (alphaDummy011 x y)),
                              (alphaDummy002, y), (alphaDummy001, x),
                              (alphaDummy004, (alphaDummy005 x y z w))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy018, (alphaDummy019 x y)),
                              (alphaDummy014, (alphaDummy016 x y)),
                              (alphaDummy015, (alphaDummy017 x y)),
                              (alphaDummy040, (alphaDummy041 x y)),
                              (alphaDummy038, (alphaDummy039 x y)),
                              (alphaDummy007, (alphaDummy009 x y)),
                              (alphaDummy006, (alphaDummy008 x y)),
                              (alphaDummy036, (alphaDummy037 x y)),
                              (alphaDummy010, (alphaDummy011 x y)),
                              (alphaDummy002, y), (alphaDummy001, x),
                              (alphaDummy004, (alphaDummy005 x y z w))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `swapped_variable`. -/
@[expose]
def swappedVariable (x y z w : Var) :
    TAlphaClass
      [(alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, alphaDummy005 x y z w)]
      (Class.cv alphaDummy004) (Class.cv (alphaDummy005 x y z w)) :=
  by
  have leftSecond : alphaDummy002 ≠ alphaDummy004 :=
    by
    unfold alphaDummy004
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)
  have rightSecond : y ≠ alphaDummy005 x y z w :=
    by
    unfold alphaDummy005
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0003 x y z w) 0)
  have leftFirst : alphaDummy001 ≠ alphaDummy004 :=
    by
    unfold alphaDummy004
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)
  have rightFirst : x ≠ alphaDummy005 x y z w :=
    by
    unfold alphaDummy005
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0001 x y z w) 0)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there leftSecond.symm rightSecond.symm
          (TAlphaVar.there leftFirst.symm rightFirst.symm (TAlphaVar.here _ _ _))))

/-- Proof-translation construction identified upstream as `split_alpha_0004`. -/
@[expose]
noncomputable def splitAlpha0004 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [(alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.classEq (Class.cv alphaDummy004)
        (synCop (Class.cv alphaDummy001) (Class.cv alphaDummy002)))
      (Wff.classEq (Class.cv (alphaDummy005 x y z w)) (synCop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (swappedVariable x y z w) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0001 x y z w dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0001 x y z w dv_x_y)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪
                                    ((Class.cv alphaDummy002)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (splitAlpha0003 x y z w)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [(alphaDummy038, (alphaDummy039 x y)),
                                        (alphaDummy007, (alphaDummy009 x y)),
                                        (alphaDummy006, (alphaDummy008 x y)),
                                        (alphaDummy036, (alphaDummy037 x y)),
                                        (alphaDummy010, (alphaDummy011 x y)),
                                        (alphaDummy002, y), (alphaDummy001, x),
                                        (alphaDummy004, (alphaDummy005 x y z w))]
                                      (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪
                                    ((Class.cv alphaDummy002)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (splitAlpha0003 x y z w)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [(alphaDummy038, (alphaDummy039 x y)),
                                        (alphaDummy007, (alphaDummy009 x y)),
                                        (alphaDummy006, (alphaDummy008 x y)),
                                        (alphaDummy036, (alphaDummy037 x y)),
                                        (alphaDummy010, (alphaDummy011 x y)),
                                        (alphaDummy002, y), (alphaDummy001, x),
                                        (alphaDummy004, (alphaDummy005 x y z w))]
                                      (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0005`. -/
@[expose]
noncomputable def splitAlpha0005 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy058, (alphaDummy061 z w)), (alphaDummy057, (alphaDummy060 z w)),
        (alphaDummy056, (alphaDummy059 z w)),
        (alphaDummy054, (alphaDummy055 z w)),
        (alphaDummy050, (alphaDummy052 z w)),
        (alphaDummy051, (alphaDummy053 z w)),
        (alphaDummy043, (alphaDummy045 z w)),
        (alphaDummy042, (alphaDummy044 z w)),
        (alphaDummy048, (alphaDummy049 z w)),
        (alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy057) (Class.cv alphaDummy058))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy056)
            (synCun (Class.cv alphaDummy057) (Class.cv alphaDummy058)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy060 z w)) (Class.cv (alphaDummy061 z w))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy059 z w))
            (synCun (Class.cv (alphaDummy060 z w)) (Class.cv (alphaDummy061 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy058, (alphaDummy061 z w)), (alphaDummy057, (alphaDummy060 z w)),
          (alphaDummy056, (alphaDummy059 z w)), (alphaDummy054, (alphaDummy055 z w)),
          (alphaDummy050, (alphaDummy052 z w)), (alphaDummy051, (alphaDummy053 z w)),
          (alphaDummy043, (alphaDummy045 z w)), (alphaDummy042, (alphaDummy044 z w)),
          (alphaDummy048, (alphaDummy049 z w)),
          (alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w),
          (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
          (alphaDummy004, (alphaDummy005 x y z w))] (synC0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0006`. -/
@[expose]
noncomputable def splitAlpha0006 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [(alphaDummy043, (alphaDummy045 z w)), (alphaDummy042, (alphaDummy044 z w)),
        (alphaDummy048, (alphaDummy049 z w)),
        (alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy043) (Class.cv alphaDummy003)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy042) (synCphi (Class.cv alphaDummy043)))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy045 z w)) (Class.cv z)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy044 z w))
            (synCphi (Class.cv (alphaDummy045 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 z w) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 z w) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0047 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0045 z w) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_w_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv alphaDummy003)).fv ∪ ((Class.cv alphaDummy000)).fv) (by decide))
            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy043)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy045 z w))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0053 z w) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0051 z w) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy058, (alphaDummy061 z w)),
        (alphaDummy057, (alphaDummy060 z w)), (alphaDummy056, (alphaDummy059 z w)),
        (alphaDummy054, (alphaDummy055 z w)), (alphaDummy050, (alphaDummy052 z w)),
        (alphaDummy051, (alphaDummy053 z w)), (alphaDummy043, (alphaDummy045 z w)),
        (alphaDummy042, (alphaDummy044 z w)), (alphaDummy048, (alphaDummy049 z w)),
        (alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w), (alphaDummy003, z),
        (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0005 x y z w))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy054, (alphaDummy055 z w)),
                              (alphaDummy050, (alphaDummy052 z w)),
                              (alphaDummy051, (alphaDummy053 z w)),
                              (alphaDummy043, (alphaDummy045 z w)),
                              (alphaDummy042, (alphaDummy044 z w)),
                              (alphaDummy048, (alphaDummy049 z w)),
                              (alphaDummy046, (alphaDummy047 z w)),
                              (alphaDummy000, w), (alphaDummy003, z),
                              (alphaDummy002, y), (alphaDummy001, x),
                              (alphaDummy004, (alphaDummy005 x y z w))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy054, (alphaDummy055 z w)),
                              (alphaDummy050, (alphaDummy052 z w)),
                              (alphaDummy051, (alphaDummy053 z w)),
                              (alphaDummy043, (alphaDummy045 z w)),
                              (alphaDummy042, (alphaDummy044 z w)),
                              (alphaDummy048, (alphaDummy049 z w)),
                              (alphaDummy046, (alphaDummy047 z w)),
                              (alphaDummy000, w), (alphaDummy003, z),
                              (alphaDummy002, y), (alphaDummy001, x),
                              (alphaDummy004, (alphaDummy005 x y z w))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0007`. -/
@[expose]
noncomputable def splitAlpha0007 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy058, (alphaDummy061 z w)), (alphaDummy057, (alphaDummy060 z w)),
        (alphaDummy056, (alphaDummy059 z w)),
        (alphaDummy054, (alphaDummy055 z w)),
        (alphaDummy050, (alphaDummy052 z w)),
        (alphaDummy051, (alphaDummy053 z w)),
        (alphaDummy076, (alphaDummy077 z w)),
        (alphaDummy074, (alphaDummy075 z w)),
        (alphaDummy043, (alphaDummy045 z w)),
        (alphaDummy042, (alphaDummy044 z w)),
        (alphaDummy072, (alphaDummy073 z w)),
        (alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy057) (Class.cv alphaDummy058))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy056)
            (synCun (Class.cv alphaDummy057) (Class.cv alphaDummy058)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy060 z w)) (Class.cv (alphaDummy061 z w))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy059 z w))
            (synCun (Class.cv (alphaDummy060 z w)) (Class.cv (alphaDummy061 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy058, (alphaDummy061 z w)), (alphaDummy057, (alphaDummy060 z w)),
          (alphaDummy056, (alphaDummy059 z w)), (alphaDummy054, (alphaDummy055 z w)),
          (alphaDummy050, (alphaDummy052 z w)), (alphaDummy051, (alphaDummy053 z w)),
          (alphaDummy076, (alphaDummy077 z w)), (alphaDummy074, (alphaDummy075 z w)),
          (alphaDummy043, (alphaDummy045 z w)), (alphaDummy042, (alphaDummy044 z w)),
          (alphaDummy072, (alphaDummy073 z w)),
          (alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w),
          (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
          (alphaDummy004, (alphaDummy005 x y z w))] (synC0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy050)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy052 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0008`. -/
@[expose]
noncomputable def splitAlpha0008 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy051, (alphaDummy053 z w)), (alphaDummy076, (alphaDummy077 z w)),
        (alphaDummy074, (alphaDummy075 z w)),
        (alphaDummy043, (alphaDummy045 z w)),
        (alphaDummy042, (alphaDummy044 z w)),
        (alphaDummy072, (alphaDummy073 z w)),
        (alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.all alphaDummy050 (Wff.neg
          (synWa (Wff.classMem (Class.cv alphaDummy050) (Class.cv alphaDummy043))
            (Wff.classEq (Class.cv alphaDummy051)
              (synCif (Wff.classMem (Class.cv alphaDummy050) (synCnnc))
                (synCplc (Class.cv alphaDummy050) (synC1c)) (Class.cv alphaDummy050))))))
      (Wff.all (alphaDummy052 z w) (Wff.neg (synWa
            (Wff.classMem (Class.cv (alphaDummy052 z w)) (Class.cv (alphaDummy045 z w)))
            (Wff.classEq (Class.cv (alphaDummy053 z w))
              (synCif (Wff.classMem (Class.cv (alphaDummy052 z w)) (synCnnc))
                (synCplc (Class.cv (alphaDummy052 z w)) (synC1c))
                (Class.cv (alphaDummy052 z w))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0078 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 z w) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 z w) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective (((Class.cv alphaDummy043)).fv) (by decide))
              (freshVar_injective (((Class.cv (alphaDummy045 z w))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [(alphaDummy058, (alphaDummy061 z w)),
                                    (alphaDummy057, (alphaDummy060 z w)),
                                    (alphaDummy056, (alphaDummy059 z w)),
                                    (alphaDummy054, (alphaDummy055 z w)),
                                    (alphaDummy050, (alphaDummy052 z w)),
                                    (alphaDummy051, (alphaDummy053 z w)),
                                    (alphaDummy076, (alphaDummy077 z w)),
                                    (alphaDummy074, (alphaDummy075 z w)),
                                    (alphaDummy043, (alphaDummy045 z w)),
                                    (alphaDummy042, (alphaDummy044 z w)),
                                    (alphaDummy072, (alphaDummy073 z w)),
                                    (alphaDummy046, (alphaDummy047 z w)),
                                    (alphaDummy000, w), (alphaDummy003, z),
                                    (alphaDummy002, y), (alphaDummy001, x),
                                    (alphaDummy004, (alphaDummy005 x y z w))]
                                  (synC1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (splitAlpha0007 x y z w))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [(alphaDummy054, (alphaDummy055 z w)),
                        (alphaDummy050, (alphaDummy052 z w)),
                        (alphaDummy051, (alphaDummy053 z w)),
                        (alphaDummy076, (alphaDummy077 z w)),
                        (alphaDummy074, (alphaDummy075 z w)),
                        (alphaDummy043, (alphaDummy045 z w)),
                        (alphaDummy042, (alphaDummy044 z w)),
                        (alphaDummy072, (alphaDummy073 z w)),
                        (alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w),
                        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
                        (alphaDummy004, (alphaDummy005 x y z w))]
                      (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [(alphaDummy054, (alphaDummy055 z w)),
                        (alphaDummy050, (alphaDummy052 z w)),
                        (alphaDummy051, (alphaDummy053 z w)),
                        (alphaDummy076, (alphaDummy077 z w)),
                        (alphaDummy074, (alphaDummy075 z w)),
                        (alphaDummy043, (alphaDummy045 z w)),
                        (alphaDummy042, (alphaDummy044 z w)),
                        (alphaDummy072, (alphaDummy073 z w)),
                        (alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w),
                        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
                        (alphaDummy004, (alphaDummy005 x y z w))]
                      (synCnnc) (by simp only [fv_syn_cnnc])))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0009`. -/
@[expose]
noncomputable def splitAlpha0009 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [(alphaDummy046, (alphaDummy047 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy046) (synCcompl (Class.cab alphaDummy042
              (synWrex alphaDummy043 (Class.cv alphaDummy003)
                (Wff.classEq (Class.cv alphaDummy042)
                  (synCphi (Class.cv alphaDummy043))))))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy046) (synCcompl (Class.cab alphaDummy042
                (synWrex alphaDummy043 (Class.cv alphaDummy000)
                  (Wff.classEq (Class.cv alphaDummy042)
                    (synCun (synCphi (Class.cv alphaDummy043)) (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy047 z w)) (synCcompl
            (Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy044 z w))
                  (synCphi (Class.cv (alphaDummy045 z w)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy047 z w)) (synCcompl
              (Class.cab (alphaDummy044 z w) (synWrex (alphaDummy045 z w) (Class.cv w)
                  (Wff.classEq (Class.cv (alphaDummy044 z w))
                    (synCun (synCphi (Class.cv (alphaDummy045 z w)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0006 x y z w dv_w_z)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0006 x y z w dv_w_z)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 1))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv alphaDummy003)).fv ∪
                                ((Class.cv alphaDummy000)).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [(alphaDummy074, (alphaDummy075 z w)),
                                    (alphaDummy043, (alphaDummy045 z w)),
                                    (alphaDummy042, (alphaDummy044 z w)),
                                    (alphaDummy072, (alphaDummy073 z w)),
                                    (alphaDummy046, (alphaDummy047 z w)),
                                    (alphaDummy000, w), (alphaDummy003, z),
                                    (alphaDummy002, y), (alphaDummy001, x),
                                    (alphaDummy004, (alphaDummy005 x y z w))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 1))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv alphaDummy003)).fv ∪
                                ((Class.cv alphaDummy000)).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [(alphaDummy074, (alphaDummy075 z w)),
                                    (alphaDummy043, (alphaDummy045 z w)),
                                    (alphaDummy042, (alphaDummy044 z w)),
                                    (alphaDummy072, (alphaDummy073 z w)),
                                    (alphaDummy046, (alphaDummy047 z w)),
                                    (alphaDummy000, w), (alphaDummy003, z),
                                    (alphaDummy002, y), (alphaDummy001, x),
                                    (alphaDummy004, (alphaDummy005 x y z w))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0010`. -/
@[expose]
noncomputable def splitAlpha0010 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy094, (alphaDummy097 z w)), (alphaDummy093, (alphaDummy096 z w)),
        (alphaDummy092, (alphaDummy095 z w)),
        (alphaDummy090, (alphaDummy091 z w)),
        (alphaDummy086, (alphaDummy088 z w)),
        (alphaDummy087, (alphaDummy089 z w)),
        (alphaDummy079, (alphaDummy081 z w)),
        (alphaDummy078, (alphaDummy080 z w)),
        (alphaDummy084, (alphaDummy085 z w)),
        (alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy093) (Class.cv alphaDummy094))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy092)
            (synCun (Class.cv alphaDummy093) (Class.cv alphaDummy094)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy096 z w)) (Class.cv (alphaDummy097 z w))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy095 z w))
            (synCun (Class.cv (alphaDummy096 z w)) (Class.cv (alphaDummy097 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy094, (alphaDummy097 z w)), (alphaDummy093, (alphaDummy096 z w)),
          (alphaDummy092, (alphaDummy095 z w)), (alphaDummy090, (alphaDummy091 z w)),
          (alphaDummy086, (alphaDummy088 z w)), (alphaDummy087, (alphaDummy089 z w)),
          (alphaDummy079, (alphaDummy081 z w)), (alphaDummy078, (alphaDummy080 z w)),
          (alphaDummy084, (alphaDummy085 z w)),
          (alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w),
          (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
          (alphaDummy004, (alphaDummy005 x y z w))] (synC0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0011`. -/
@[expose]
noncomputable def splitAlpha0011 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy079, (alphaDummy081 z w)), (alphaDummy078, (alphaDummy080 z w)),
        (alphaDummy084, (alphaDummy085 z w)),
        (alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy079) (Class.cv alphaDummy000)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy078) (synCphi (Class.cv alphaDummy079)))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy081 z w)) (Class.cv w)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy080 z w))
            (synCphi (Class.cv (alphaDummy081 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 z w) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 z w) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0084 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0085 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0081 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0083 z w) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy003)).fv) (by decide))
            (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 z w) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 z w) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy079)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy081 z w))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 z w) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0090 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0091 z w) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0089 z w) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy094, (alphaDummy097 z w)),
        (alphaDummy093, (alphaDummy096 z w)), (alphaDummy092, (alphaDummy095 z w)),
        (alphaDummy090, (alphaDummy091 z w)), (alphaDummy086, (alphaDummy088 z w)),
        (alphaDummy087, (alphaDummy089 z w)), (alphaDummy079, (alphaDummy081 z w)),
        (alphaDummy078, (alphaDummy080 z w)), (alphaDummy084, (alphaDummy085 z w)),
        (alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w), (alphaDummy003, z),
        (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0010 x y z w))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy090, (alphaDummy091 z w)),
                              (alphaDummy086, (alphaDummy088 z w)),
                              (alphaDummy087, (alphaDummy089 z w)),
                              (alphaDummy079, (alphaDummy081 z w)),
                              (alphaDummy078, (alphaDummy080 z w)),
                              (alphaDummy084, (alphaDummy085 z w)),
                              (alphaDummy082, (alphaDummy083 z w)),
                              (alphaDummy000, w), (alphaDummy003, z),
                              (alphaDummy002, y), (alphaDummy001, x),
                              (alphaDummy004, (alphaDummy005 x y z w))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy090, (alphaDummy091 z w)),
                              (alphaDummy086, (alphaDummy088 z w)),
                              (alphaDummy087, (alphaDummy089 z w)),
                              (alphaDummy079, (alphaDummy081 z w)),
                              (alphaDummy078, (alphaDummy080 z w)),
                              (alphaDummy084, (alphaDummy085 z w)),
                              (alphaDummy082, (alphaDummy083 z w)),
                              (alphaDummy000, w), (alphaDummy003, z),
                              (alphaDummy002, y), (alphaDummy001, x),
                              (alphaDummy004, (alphaDummy005 x y z w))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0012`. -/
@[expose]
noncomputable def splitAlpha0012 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy094, (alphaDummy097 z w)), (alphaDummy093, (alphaDummy096 z w)),
        (alphaDummy092, (alphaDummy095 z w)),
        (alphaDummy090, (alphaDummy091 z w)),
        (alphaDummy086, (alphaDummy088 z w)),
        (alphaDummy087, (alphaDummy089 z w)),
        (alphaDummy112, (alphaDummy113 z w)),
        (alphaDummy110, (alphaDummy111 z w)),
        (alphaDummy079, (alphaDummy081 z w)),
        (alphaDummy078, (alphaDummy080 z w)),
        (alphaDummy108, (alphaDummy109 z w)),
        (alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy093) (Class.cv alphaDummy094))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy092)
            (synCun (Class.cv alphaDummy093) (Class.cv alphaDummy094)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy096 z w)) (Class.cv (alphaDummy097 z w))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy095 z w))
            (synCun (Class.cv (alphaDummy096 z w)) (Class.cv (alphaDummy097 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy094, (alphaDummy097 z w)), (alphaDummy093, (alphaDummy096 z w)),
          (alphaDummy092, (alphaDummy095 z w)), (alphaDummy090, (alphaDummy091 z w)),
          (alphaDummy086, (alphaDummy088 z w)), (alphaDummy087, (alphaDummy089 z w)),
          (alphaDummy112, (alphaDummy113 z w)), (alphaDummy110, (alphaDummy111 z w)),
          (alphaDummy079, (alphaDummy081 z w)), (alphaDummy078, (alphaDummy080 z w)),
          (alphaDummy108, (alphaDummy109 z w)),
          (alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w),
          (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
          (alphaDummy004, (alphaDummy005 x y z w))] (synC0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy086)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy088 z w))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0013`. -/
@[expose]
noncomputable def splitAlpha0013 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alphaDummy087, (alphaDummy089 z w)), (alphaDummy112, (alphaDummy113 z w)),
        (alphaDummy110, (alphaDummy111 z w)),
        (alphaDummy079, (alphaDummy081 z w)),
        (alphaDummy078, (alphaDummy080 z w)),
        (alphaDummy108, (alphaDummy109 z w)),
        (alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.all alphaDummy086 (Wff.neg
          (synWa (Wff.classMem (Class.cv alphaDummy086) (Class.cv alphaDummy079))
            (Wff.classEq (Class.cv alphaDummy087)
              (synCif (Wff.classMem (Class.cv alphaDummy086) (synCnnc))
                (synCplc (Class.cv alphaDummy086) (synC1c)) (Class.cv alphaDummy086))))))
      (Wff.all (alphaDummy088 z w) (Wff.neg (synWa
            (Wff.classMem (Class.cv (alphaDummy088 z w)) (Class.cv (alphaDummy081 z w)))
            (Wff.classEq (Class.cv (alphaDummy089 z w))
              (synCif (Wff.classMem (Class.cv (alphaDummy088 z w)) (synCnnc))
                (synCplc (Class.cv (alphaDummy088 z w)) (synC1c))
                (Class.cv (alphaDummy088 z w))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 1))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 z w) 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0116 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0117 z w) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0114 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0115 z w) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective (((Class.cv alphaDummy079)).fv) (by decide))
              (freshVar_injective (((Class.cv (alphaDummy081 z w))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 z w) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 z w) 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [(alphaDummy094, (alphaDummy097 z w)),
                                    (alphaDummy093, (alphaDummy096 z w)),
                                    (alphaDummy092, (alphaDummy095 z w)),
                                    (alphaDummy090, (alphaDummy091 z w)),
                                    (alphaDummy086, (alphaDummy088 z w)),
                                    (alphaDummy087, (alphaDummy089 z w)),
                                    (alphaDummy112, (alphaDummy113 z w)),
                                    (alphaDummy110, (alphaDummy111 z w)),
                                    (alphaDummy079, (alphaDummy081 z w)),
                                    (alphaDummy078, (alphaDummy080 z w)),
                                    (alphaDummy108, (alphaDummy109 z w)),
                                    (alphaDummy082, (alphaDummy083 z w)),
                                    (alphaDummy000, w), (alphaDummy003, z),
                                    (alphaDummy002, y), (alphaDummy001, x),
                                    (alphaDummy004, (alphaDummy005 x y z w))]
                                  (synC1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (splitAlpha0012 x y z w))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [(alphaDummy090, (alphaDummy091 z w)),
                        (alphaDummy086, (alphaDummy088 z w)),
                        (alphaDummy087, (alphaDummy089 z w)),
                        (alphaDummy112, (alphaDummy113 z w)),
                        (alphaDummy110, (alphaDummy111 z w)),
                        (alphaDummy079, (alphaDummy081 z w)),
                        (alphaDummy078, (alphaDummy080 z w)),
                        (alphaDummy108, (alphaDummy109 z w)),
                        (alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w),
                        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
                        (alphaDummy004, (alphaDummy005 x y z w))]
                      (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [(alphaDummy090, (alphaDummy091 z w)),
                        (alphaDummy086, (alphaDummy088 z w)),
                        (alphaDummy087, (alphaDummy089 z w)),
                        (alphaDummy112, (alphaDummy113 z w)),
                        (alphaDummy110, (alphaDummy111 z w)),
                        (alphaDummy079, (alphaDummy081 z w)),
                        (alphaDummy078, (alphaDummy080 z w)),
                        (alphaDummy108, (alphaDummy109 z w)),
                        (alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w),
                        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
                        (alphaDummy004, (alphaDummy005 x y z w))]
                      (synCnnc) (by simp only [fv_syn_cnnc])))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0014`. -/
@[expose]
noncomputable def splitAlpha0014 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [(alphaDummy082, (alphaDummy083 z w)), (alphaDummy000, w),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x),
        (alphaDummy004, (alphaDummy005 x y z w))]
      (Wff.classMem (Class.cv alphaDummy082) (synCcompl (Class.cab alphaDummy078
            (synWrex alphaDummy079 (Class.cv alphaDummy003)
              (Wff.classEq (Class.cv alphaDummy078)
                (synCun (synCphi (Class.cv alphaDummy079)) (synCsn (synC0c))))))))
      (Wff.classMem (Class.cv (alphaDummy083 z w)) (synCcompl
          (Class.cab (alphaDummy080 z w) (synWrex (alphaDummy081 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alphaDummy080 z w))
                (synCun (synCphi (Class.cv (alphaDummy081 z w)))
                  (synCsn (synC0c)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 1))
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0112 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0113 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0109 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0111 z w) 0))
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_w_z) (TAlphaVar.here _ _ _))))))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy003)).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (splitAlpha0013 x y z w))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab
                                      (TAlphaWff.neg (splitAlpha0013 x y z w))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.reflOfClosed
                              [(alphaDummy110, (alphaDummy111 z w)),
                                (alphaDummy079, (alphaDummy081 z w)),
                                (alphaDummy078, (alphaDummy080 z w)),
                                (alphaDummy108, (alphaDummy109 z w)),
                                (alphaDummy082, (alphaDummy083 z w)),
                                (alphaDummy000, w), (alphaDummy003, z),
                                (alphaDummy002, y), (alphaDummy001, x),
                                (alphaDummy004, (alphaDummy005 x y z w))]
                              (synCcompl (synCsn (synC0c))) (by
                                simp only [fv_syn_ccompl, fv_syn_csn,
                                  fv_syn_c0c])))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 1))
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0112 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0113 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0109 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0111 z w) 0))
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_w_z) (TAlphaVar.here _ _ _))))))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy003)).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (splitAlpha0013 x y z w))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab
                                      (TAlphaWff.neg (splitAlpha0013 x y z w))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.reflOfClosed
                              [(alphaDummy110, (alphaDummy111 z w)),
                                (alphaDummy079, (alphaDummy081 z w)),
                                (alphaDummy078, (alphaDummy080 z w)),
                                (alphaDummy108, (alphaDummy109 z w)),
                                (alphaDummy082, (alphaDummy083 z w)),
                                (alphaDummy000, w), (alphaDummy003, z),
                                (alphaDummy002, y), (alphaDummy001, x),
                                (alphaDummy004, (alphaDummy005 x y z w))]
                              (synCcompl (synCsn (synC0c))) (by
                                simp only [fv_syn_ccompl, fv_syn_csn,
                                  fv_syn_c0c])))))))))))))))

end SwapAlpha

/-- Checked nominal proof certificate identified upstream as `nominal_df_swap`. -/
@[expose]
noncomputable def nominalDfSwap (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
    (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCswap) (synCopab x y (synWex z (synWex w
              (synWa (.classEq (.cv x) (synCop (.cv z) (.cv w)))
                (.classEq (.cv y) (synCop (.cv w) (.cv z)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (SwapAlpha.splitAlpha0004 x y z w dv_x_y) (TAlphaWff.ex
                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (Ne.symm dv_w_x) (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                              (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.neg (SwapAlpha.splitAlpha0009 x y z w dv_w_z)))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_y)
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (SwapAlpha.splitAlpha0011 x y z w))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.neg
        (SwapAlpha.splitAlpha0011 x y z w)))))))))
                            (SwapAlpha.splitAlpha0014 x y z w dv_w_z))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
