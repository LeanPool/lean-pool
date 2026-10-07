/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.SecondProjectionAlpha


/-! NF weak partition development: NominalAlphaRepairedBase001048Leaf2ndReflected001. -/


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


namespace SecondProjectionAlpha

/-- Proof-translation construction identified upstream as `split_alpha_0000`. -/
@[expose]
noncomputable def splitAlpha0000 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alphaDummy021, (alphaDummy024 x y)), (alphaDummy020, (alphaDummy023 x y)),
        (alphaDummy019, (alphaDummy022 x y)),
        (alphaDummy017, (alphaDummy018 x y)),
        (alphaDummy013, (alphaDummy015 x y)),
        (alphaDummy014, (alphaDummy016 x y)),
        (alphaDummy006, (alphaDummy008 x y)),
        (alphaDummy005, (alphaDummy007 x y)),
        (alphaDummy011, (alphaDummy012 x y)),
        (alphaDummy009, (alphaDummy010 x y)), (alphaDummy001, y),
        (alphaDummy000, x), (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy020) (Class.cv alphaDummy021))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy019)
            (synCun (Class.cv alphaDummy020) (Class.cv alphaDummy021)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy022 x y))
            (synCun (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
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
                                (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy021, (alphaDummy024 x y)), (alphaDummy020, (alphaDummy023 x y)),
          (alphaDummy019, (alphaDummy022 x y)), (alphaDummy017, (alphaDummy018 x y)),
          (alphaDummy013, (alphaDummy015 x y)), (alphaDummy014, (alphaDummy016 x y)),
          (alphaDummy006, (alphaDummy008 x y)), (alphaDummy005, (alphaDummy007 x y)),
          (alphaDummy011, (alphaDummy012 x y)),
          (alphaDummy009, (alphaDummy010 x y)), (alphaDummy001, y),
          (alphaDummy000, x), (alphaDummy003, (alphaDummy004 x y z))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
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
noncomputable def splitAlpha0001 (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [(alphaDummy006, (alphaDummy008 x y)), (alphaDummy005, (alphaDummy007 x y)),
        (alphaDummy011, (alphaDummy012 x y)),
        (alphaDummy009, (alphaDummy010 x y)), (alphaDummy001, y),
        (alphaDummy000, x), (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy006) (Class.cv alphaDummy000)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy005) (synCphi (Class.cv alphaDummy006)))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy008 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy007 x y))
            (synCphi (Class.cv (alphaDummy008 x y)))))) :=
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
              (((Class.cv alphaDummy000)).fv ∪ ((Class.cv alphaDummy001)).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy006)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy008 x y))).fv) (by decide))
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
                                        [(alphaDummy021, (alphaDummy024 x y)),
        (alphaDummy020, (alphaDummy023 x y)), (alphaDummy019, (alphaDummy022 x y)),
        (alphaDummy017, (alphaDummy018 x y)), (alphaDummy013, (alphaDummy015 x y)),
        (alphaDummy014, (alphaDummy016 x y)), (alphaDummy006, (alphaDummy008 x y)),
        (alphaDummy005, (alphaDummy007 x y)), (alphaDummy011, (alphaDummy012 x y)),
        (alphaDummy009, (alphaDummy010 x y)), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy003, (alphaDummy004 x y z))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0000 x y z))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy017, (alphaDummy018 x y)),
                              (alphaDummy013, (alphaDummy015 x y)),
                              (alphaDummy014, (alphaDummy016 x y)),
                              (alphaDummy006, (alphaDummy008 x y)),
                              (alphaDummy005, (alphaDummy007 x y)),
                              (alphaDummy011, (alphaDummy012 x y)),
                              (alphaDummy009, (alphaDummy010 x y)),
                              (alphaDummy001, y), (alphaDummy000, x),
                              (alphaDummy003, (alphaDummy004 x y z))]
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
                            [(alphaDummy017, (alphaDummy018 x y)),
                              (alphaDummy013, (alphaDummy015 x y)),
                              (alphaDummy014, (alphaDummy016 x y)),
                              (alphaDummy006, (alphaDummy008 x y)),
                              (alphaDummy005, (alphaDummy007 x y)),
                              (alphaDummy011, (alphaDummy012 x y)),
                              (alphaDummy009, (alphaDummy010 x y)),
                              (alphaDummy001, y), (alphaDummy000, x),
                              (alphaDummy003, (alphaDummy004 x y z))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0002`. -/
@[expose]
noncomputable def splitAlpha0002 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alphaDummy021, (alphaDummy024 x y)), (alphaDummy020, (alphaDummy023 x y)),
        (alphaDummy019, (alphaDummy022 x y)),
        (alphaDummy017, (alphaDummy018 x y)),
        (alphaDummy013, (alphaDummy015 x y)),
        (alphaDummy014, (alphaDummy016 x y)),
        (alphaDummy039, (alphaDummy040 x y)),
        (alphaDummy037, (alphaDummy038 x y)),
        (alphaDummy006, (alphaDummy008 x y)),
        (alphaDummy005, (alphaDummy007 x y)),
        (alphaDummy035, (alphaDummy036 x y)),
        (alphaDummy009, (alphaDummy010 x y)), (alphaDummy001, y),
        (alphaDummy000, x), (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy020) (Class.cv alphaDummy021))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy019)
            (synCun (Class.cv alphaDummy020) (Class.cv alphaDummy021)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy022 x y))
            (synCun (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
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
                                (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy021, (alphaDummy024 x y)), (alphaDummy020, (alphaDummy023 x y)),
          (alphaDummy019, (alphaDummy022 x y)), (alphaDummy017, (alphaDummy018 x y)),
          (alphaDummy013, (alphaDummy015 x y)), (alphaDummy014, (alphaDummy016 x y)),
          (alphaDummy039, (alphaDummy040 x y)), (alphaDummy037, (alphaDummy038 x y)),
          (alphaDummy006, (alphaDummy008 x y)), (alphaDummy005, (alphaDummy007 x y)),
          (alphaDummy035, (alphaDummy036 x y)),
          (alphaDummy009, (alphaDummy010 x y)), (alphaDummy001, y),
          (alphaDummy000, x), (alphaDummy003, (alphaDummy004 x y z))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy013)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
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
noncomputable def splitAlpha0003 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alphaDummy039, (alphaDummy040 x y)), (alphaDummy037, (alphaDummy038 x y)),
        (alphaDummy006, (alphaDummy008 x y)),
        (alphaDummy005, (alphaDummy007 x y)),
        (alphaDummy035, (alphaDummy036 x y)),
        (alphaDummy009, (alphaDummy010 x y)), (alphaDummy001, y),
        (alphaDummy000, x), (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy039) (synCphi (Class.cv alphaDummy006)))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy039)
            (synCphi (Class.cv alphaDummy006)))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy040 x y))
          (synCphi (Class.cv (alphaDummy008 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy040 x y))
            (synCphi (Class.cv (alphaDummy008 x y)))))) :=
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
                  (freshVar_injective (((Class.cv alphaDummy006)).fv) (by decide))
                  (freshVar_injective (((Class.cv (alphaDummy008 x y))).fv) (by decide))
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
                                      [(alphaDummy021, (alphaDummy024 x y)),
                                        (alphaDummy020, (alphaDummy023 x y)),
                                        (alphaDummy019, (alphaDummy022 x y)),
                                        (alphaDummy017, (alphaDummy018 x y)),
                                        (alphaDummy013, (alphaDummy015 x y)),
                                        (alphaDummy014, (alphaDummy016 x y)),
                                        (alphaDummy039, (alphaDummy040 x y)),
                                        (alphaDummy037, (alphaDummy038 x y)),
                                        (alphaDummy006, (alphaDummy008 x y)),
                                        (alphaDummy005, (alphaDummy007 x y)),
                                        (alphaDummy035, (alphaDummy036 x y)),
                                        (alphaDummy009, (alphaDummy010 x y)),
                                        (alphaDummy001, y), (alphaDummy000, x),
                                        (alphaDummy003, (alphaDummy004 x y z))]
                                      (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (splitAlpha0002 x y z))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [(alphaDummy017, (alphaDummy018 x y)),
                            (alphaDummy013, (alphaDummy015 x y)),
                            (alphaDummy014, (alphaDummy016 x y)),
                            (alphaDummy039, (alphaDummy040 x y)),
                            (alphaDummy037, (alphaDummy038 x y)),
                            (alphaDummy006, (alphaDummy008 x y)),
                            (alphaDummy005, (alphaDummy007 x y)),
                            (alphaDummy035, (alphaDummy036 x y)),
                            (alphaDummy009, (alphaDummy010 x y)),
                            (alphaDummy001, y), (alphaDummy000, x),
                            (alphaDummy003, (alphaDummy004 x y z))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [(alphaDummy017, (alphaDummy018 x y)),
                            (alphaDummy013, (alphaDummy015 x y)),
                            (alphaDummy014, (alphaDummy016 x y)),
                            (alphaDummy039, (alphaDummy040 x y)),
                            (alphaDummy037, (alphaDummy038 x y)),
                            (alphaDummy006, (alphaDummy008 x y)),
                            (alphaDummy005, (alphaDummy007 x y)),
                            (alphaDummy035, (alphaDummy036 x y)),
                            (alphaDummy009, (alphaDummy010 x y)),
                            (alphaDummy001, y), (alphaDummy000, x),
                            (alphaDummy003, (alphaDummy004 x y z))]
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
                    (freshVar_injective (((Class.cv alphaDummy006)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy008 x y))).fv) (by decide))
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
                                        [(alphaDummy021, (alphaDummy024 x y)),
        (alphaDummy020, (alphaDummy023 x y)), (alphaDummy019, (alphaDummy022 x y)),
        (alphaDummy017, (alphaDummy018 x y)), (alphaDummy013, (alphaDummy015 x y)),
        (alphaDummy014, (alphaDummy016 x y)), (alphaDummy039, (alphaDummy040 x y)),
        (alphaDummy037, (alphaDummy038 x y)), (alphaDummy006, (alphaDummy008 x y)),
        (alphaDummy005, (alphaDummy007 x y)), (alphaDummy035, (alphaDummy036 x y)),
        (alphaDummy009, (alphaDummy010 x y)), (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy003, (alphaDummy004 x y z))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0002 x y z))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy017, (alphaDummy018 x y)),
                              (alphaDummy013, (alphaDummy015 x y)),
                              (alphaDummy014, (alphaDummy016 x y)),
                              (alphaDummy039, (alphaDummy040 x y)),
                              (alphaDummy037, (alphaDummy038 x y)),
                              (alphaDummy006, (alphaDummy008 x y)),
                              (alphaDummy005, (alphaDummy007 x y)),
                              (alphaDummy035, (alphaDummy036 x y)),
                              (alphaDummy009, (alphaDummy010 x y)),
                              (alphaDummy001, y), (alphaDummy000, x),
                              (alphaDummy003, (alphaDummy004 x y z))]
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
                            [(alphaDummy017, (alphaDummy018 x y)),
                              (alphaDummy013, (alphaDummy015 x y)),
                              (alphaDummy014, (alphaDummy016 x y)),
                              (alphaDummy039, (alphaDummy040 x y)),
                              (alphaDummy037, (alphaDummy038 x y)),
                              (alphaDummy006, (alphaDummy008 x y)),
                              (alphaDummy005, (alphaDummy007 x y)),
                              (alphaDummy035, (alphaDummy036 x y)),
                              (alphaDummy009, (alphaDummy010 x y)),
                              (alphaDummy001, y), (alphaDummy000, x),
                              (alphaDummy003, (alphaDummy004 x y z))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0004`. -/
@[expose]
noncomputable def splitAlpha0004 (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [(alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.classEq (Class.cv alphaDummy003)
        (synCop (Class.cv alphaDummy000) (Class.cv alphaDummy001)))
      (Wff.classEq (Class.cv (alphaDummy004 x y z)) (synCop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (TAlphaClass.cv
      (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0003 x y z) 0)))
        (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0001 x y z) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0001 x y z dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0001 x y z dv_x_y)))))))))
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
                                  (((Class.cv alphaDummy000)).fv ∪
                                    ((Class.cv alphaDummy001)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg (splitAlpha0003 x y z)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [(alphaDummy037, (alphaDummy038 x y)),
                                        (alphaDummy006, (alphaDummy008 x y)),
                                        (alphaDummy005, (alphaDummy007 x y)),
                                        (alphaDummy035, (alphaDummy036 x y)),
                                        (alphaDummy009, (alphaDummy010 x y)),
                                        (alphaDummy001, y), (alphaDummy000, x),
                                        (alphaDummy003, (alphaDummy004 x y z))]
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
                                  (((Class.cv alphaDummy000)).fv ∪
                                    ((Class.cv alphaDummy001)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg (splitAlpha0003 x y z)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [(alphaDummy037, (alphaDummy038 x y)),
                                        (alphaDummy006, (alphaDummy008 x y)),
                                        (alphaDummy005, (alphaDummy007 x y)),
                                        (alphaDummy035, (alphaDummy036 x y)),
                                        (alphaDummy009, (alphaDummy010 x y)),
                                        (alphaDummy001, y), (alphaDummy000, x),
                                        (alphaDummy003, (alphaDummy004 x y z))]
                                      (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0005`. -/
@[expose]
noncomputable def splitAlpha0005 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alphaDummy057, (alphaDummy060 y z)), (alphaDummy056, (alphaDummy059 y z)),
        (alphaDummy055, (alphaDummy058 y z)),
        (alphaDummy053, (alphaDummy054 y z)),
        (alphaDummy049, (alphaDummy051 y z)),
        (alphaDummy050, (alphaDummy052 y z)),
        (alphaDummy042, (alphaDummy044 y z)),
        (alphaDummy041, (alphaDummy043 y z)),
        (alphaDummy047, (alphaDummy048 y z)),
        (alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z),
        (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy056) (Class.cv alphaDummy057))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy055)
            (synCun (Class.cv alphaDummy056) (Class.cv alphaDummy057)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy059 y z)) (Class.cv (alphaDummy060 y z))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy058 y z))
            (synCun (Class.cv (alphaDummy059 y z)) (Class.cv (alphaDummy060 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy057, (alphaDummy060 y z)), (alphaDummy056, (alphaDummy059 y z)),
          (alphaDummy055, (alphaDummy058 y z)), (alphaDummy053, (alphaDummy054 y z)),
          (alphaDummy049, (alphaDummy051 y z)), (alphaDummy050, (alphaDummy052 y z)),
          (alphaDummy042, (alphaDummy044 y z)), (alphaDummy041, (alphaDummy043 y z)),
          (alphaDummy047, (alphaDummy048 y z)),
          (alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z),
          (alphaDummy001, y), (alphaDummy000, x),
          (alphaDummy003, (alphaDummy004 x y z))] (synC0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0006`. -/
@[expose]
noncomputable def splitAlpha0006 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alphaDummy042, (alphaDummy044 y z)), (alphaDummy041, (alphaDummy043 y z)),
        (alphaDummy047, (alphaDummy048 y z)),
        (alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z),
        (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy042) (Class.cv alphaDummy002)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy041) (synCphi (Class.cv alphaDummy042)))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy044 y z)) (Class.cv z)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy043 y z))
            (synCphi (Class.cv (alphaDummy044 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 y z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 y z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0047 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0045 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy001)).fv) (by decide))
            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alphaDummy042)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alphaDummy044 y z))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0053 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0051 y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [(alphaDummy057, (alphaDummy060 y z)),
        (alphaDummy056, (alphaDummy059 y z)), (alphaDummy055, (alphaDummy058 y z)),
        (alphaDummy053, (alphaDummy054 y z)), (alphaDummy049, (alphaDummy051 y z)),
        (alphaDummy050, (alphaDummy052 y z)), (alphaDummy042, (alphaDummy044 y z)),
        (alphaDummy041, (alphaDummy043 y z)), (alphaDummy047, (alphaDummy048 y z)),
        (alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z), (alphaDummy001, y),
        (alphaDummy000, x), (alphaDummy003, (alphaDummy004 x y z))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0005 x y z))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy053, (alphaDummy054 y z)),
                              (alphaDummy049, (alphaDummy051 y z)),
                              (alphaDummy050, (alphaDummy052 y z)),
                              (alphaDummy042, (alphaDummy044 y z)),
                              (alphaDummy041, (alphaDummy043 y z)),
                              (alphaDummy047, (alphaDummy048 y z)),
                              (alphaDummy045, (alphaDummy046 y z)),
                              (alphaDummy002, z), (alphaDummy001, y), (alphaDummy000, x),
                              (alphaDummy003, (alphaDummy004 x y z))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [(alphaDummy053, (alphaDummy054 y z)),
                              (alphaDummy049, (alphaDummy051 y z)),
                              (alphaDummy050, (alphaDummy052 y z)),
                              (alphaDummy042, (alphaDummy044 y z)),
                              (alphaDummy041, (alphaDummy043 y z)),
                              (alphaDummy047, (alphaDummy048 y z)),
                              (alphaDummy045, (alphaDummy046 y z)),
                              (alphaDummy002, z), (alphaDummy001, y), (alphaDummy000, x),
                              (alphaDummy003, (alphaDummy004 x y z))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0007`. -/
@[expose]
noncomputable def splitAlpha0007 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alphaDummy057, (alphaDummy060 y z)), (alphaDummy056, (alphaDummy059 y z)),
        (alphaDummy055, (alphaDummy058 y z)),
        (alphaDummy053, (alphaDummy054 y z)),
        (alphaDummy049, (alphaDummy051 y z)),
        (alphaDummy050, (alphaDummy052 y z)),
        (alphaDummy075, (alphaDummy076 y z)),
        (alphaDummy073, (alphaDummy074 y z)),
        (alphaDummy042, (alphaDummy044 y z)),
        (alphaDummy041, (alphaDummy043 y z)),
        (alphaDummy071, (alphaDummy072 y z)),
        (alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z),
        (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy056) (Class.cv alphaDummy057))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy055)
            (synCun (Class.cv alphaDummy056) (Class.cv alphaDummy057)))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy059 y z)) (Class.cv (alphaDummy060 y z))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy058 y z))
            (synCun (Class.cv (alphaDummy059 y z)) (Class.cv (alphaDummy060 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [(alphaDummy057, (alphaDummy060 y z)), (alphaDummy056, (alphaDummy059 y z)),
          (alphaDummy055, (alphaDummy058 y z)), (alphaDummy053, (alphaDummy054 y z)),
          (alphaDummy049, (alphaDummy051 y z)), (alphaDummy050, (alphaDummy052 y z)),
          (alphaDummy075, (alphaDummy076 y z)), (alphaDummy073, (alphaDummy074 y z)),
          (alphaDummy042, (alphaDummy044 y z)), (alphaDummy041, (alphaDummy043 y z)),
          (alphaDummy071, (alphaDummy072 y z)),
          (alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z),
          (alphaDummy001, y), (alphaDummy000, x),
          (alphaDummy003, (alphaDummy004 x y z))] (synC0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy049)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy051 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0008`. -/
@[expose]
noncomputable def splitAlpha0008 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alphaDummy075, (alphaDummy076 y z)), (alphaDummy073, (alphaDummy074 y z)),
        (alphaDummy042, (alphaDummy044 y z)),
        (alphaDummy041, (alphaDummy043 y z)),
        (alphaDummy071, (alphaDummy072 y z)),
        (alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z),
        (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.classMem (Class.cv alphaDummy075) (synCphi (Class.cv alphaDummy042)))
      (Wff.classMem (Class.cv (alphaDummy076 y z))
        (synCphi (Class.cv (alphaDummy044 y z)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 y z) 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 y z) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0078 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 y z) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy042)).fv) (by decide))
                (freshVar_injective (((Class.cv (alphaDummy044 y z))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 y z) 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 y z) 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [(alphaDummy057, (alphaDummy060 y z)),
                                      (alphaDummy056, (alphaDummy059 y z)),
                                      (alphaDummy055, (alphaDummy058 y z)),
                                      (alphaDummy053, (alphaDummy054 y z)),
                                      (alphaDummy049, (alphaDummy051 y z)),
                                      (alphaDummy050, (alphaDummy052 y z)),
                                      (alphaDummy075, (alphaDummy076 y z)),
                                      (alphaDummy073, (alphaDummy074 y z)),
                                      (alphaDummy042, (alphaDummy044 y z)),
                                      (alphaDummy041, (alphaDummy043 y z)),
                                      (alphaDummy071, (alphaDummy072 y z)),
                                      (alphaDummy045, (alphaDummy046 y z)),
                                      (alphaDummy002, z), (alphaDummy001, y),
                                      (alphaDummy000, x),
                                      (alphaDummy003, (alphaDummy004 x y z))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (splitAlpha0007 x y z))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [(alphaDummy053, (alphaDummy054 y z)),
                          (alphaDummy049, (alphaDummy051 y z)),
                          (alphaDummy050, (alphaDummy052 y z)),
                          (alphaDummy075, (alphaDummy076 y z)),
                          (alphaDummy073, (alphaDummy074 y z)),
                          (alphaDummy042, (alphaDummy044 y z)),
                          (alphaDummy041, (alphaDummy043 y z)),
                          (alphaDummy071, (alphaDummy072 y z)),
                          (alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z),
                          (alphaDummy001, y), (alphaDummy000, x),
                          (alphaDummy003, (alphaDummy004 x y z))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [(alphaDummy053, (alphaDummy054 y z)),
                          (alphaDummy049, (alphaDummy051 y z)),
                          (alphaDummy050, (alphaDummy052 y z)),
                          (alphaDummy075, (alphaDummy076 y z)),
                          (alphaDummy073, (alphaDummy074 y z)),
                          (alphaDummy042, (alphaDummy044 y z)),
                          (alphaDummy041, (alphaDummy043 y z)),
                          (alphaDummy071, (alphaDummy072 y z)),
                          (alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z),
                          (alphaDummy001, y), (alphaDummy000, x),
                          (alphaDummy003, (alphaDummy004 x y z))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0009`. -/
@[expose]
noncomputable def splitAlpha0009 (x : Var) (y : Var) (z : Var) (dv_y_z : y ≠ z) :
    TAlphaWff
      [(alphaDummy045, (alphaDummy046 y z)), (alphaDummy002, z),
        (alphaDummy001, y), (alphaDummy000, x),
        (alphaDummy003, (alphaDummy004 x y z))]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy045) (synCcompl (Class.cab alphaDummy041
              (synWrex alphaDummy042 (Class.cv alphaDummy002)
                (Wff.classEq (Class.cv alphaDummy041)
                  (synCphi (Class.cv alphaDummy042))))))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy045) (synCcompl (Class.cab alphaDummy041
                (synWrex alphaDummy042 (Class.cv alphaDummy001)
                  (Wff.classEq (Class.cv alphaDummy041)
                    (synCun (synCphi (Class.cv alphaDummy042)) (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy046 y z)) (synCcompl
            (Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy043 y z))
                  (synCphi (Class.cv (alphaDummy044 y z)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy046 y z)) (synCcompl
              (Class.cab (alphaDummy043 y z) (synWrex (alphaDummy044 y z) (Class.cv y)
                  (Wff.classEq (Class.cv (alphaDummy043 y z))
                    (synCun (synCphi (Class.cv (alphaDummy044 y z)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0006 x y z)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0006 x y z))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 1))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 y z) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 y z) 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv alphaDummy002)).fv ∪
                                ((Class.cv alphaDummy001)).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (splitAlpha0008 x y z)
                                      (splitAlpha0008 x y z)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [(alphaDummy073, (alphaDummy074 y z)),
                                    (alphaDummy042, (alphaDummy044 y z)),
                                    (alphaDummy041, (alphaDummy043 y z)),
                                    (alphaDummy071, (alphaDummy072 y z)),
                                    (alphaDummy045, (alphaDummy046 y z)),
                                    (alphaDummy002, z), (alphaDummy001, y),
                                    (alphaDummy000, x),
                                    (alphaDummy003, (alphaDummy004 x y z))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 1))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 y z) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 y z) 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv alphaDummy002)).fv ∪
                                ((Class.cv alphaDummy001)).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (splitAlpha0008 x y z)
                                      (splitAlpha0008 x y z)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [(alphaDummy073, (alphaDummy074 y z)),
                                    (alphaDummy042, (alphaDummy044 y z)),
                                    (alphaDummy041, (alphaDummy043 y z)),
                                    (alphaDummy071, (alphaDummy072 y z)),
                                    (alphaDummy045, (alphaDummy046 y z)),
                                    (alphaDummy002, z), (alphaDummy001, y),
                                    (alphaDummy000, x),
                                    (alphaDummy003, (alphaDummy004 x y z))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

end SecondProjectionAlpha

/-- Checked nominal proof certificate identified upstream as `nominal_df_2nd`. -/
@[expose]
noncomputable def nominalDf2nd (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synC2nd)
        (synCopab x y (synWex z (.classEq (.cv x) (synCop (.cv z) (.cv y)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (SecondProjectionAlpha.splitAlpha0004 x y z dv_x_y) (TAlphaWff.ex
                (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_x_y (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.neg
                        (SecondProjectionAlpha.splitAlpha0009 x y z dv_y_z))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
