/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.CompositionAlpha


/-! NF weak partition development: NominalAlphaRepairedBase001041CoReflected001. -/


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


namespace CompositionAlpha

/-- Proof-translation construction identified upstream as `split_alpha_0000`. -/
@[expose]
noncomputable def splitAlpha0000 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy021 A B), (alphaDummy024 x y)),
        ((alphaDummy020 A B), (alphaDummy023 x y)),
        ((alphaDummy019 A B), (alphaDummy022 x y)),
        ((alphaDummy017 A B), (alphaDummy018 x y)),
        ((alphaDummy013 A B), (alphaDummy015 x y)),
        ((alphaDummy014 A B), (alphaDummy016 x y)),
        ((alphaDummy006 A B), (alphaDummy008 x y)),
        ((alphaDummy005 A B), (alphaDummy007 x y)),
        ((alphaDummy011 A B), (alphaDummy012 x y)),
        ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
        ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy019 A B))
            (synCun (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy022 x y))
            (synCun (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy021 A B), (alphaDummy024 x y)),
          ((alphaDummy020 A B), (alphaDummy023 x y)),
          ((alphaDummy019 A B), (alphaDummy022 x y)),
          ((alphaDummy017 A B), (alphaDummy018 x y)),
          ((alphaDummy013 A B), (alphaDummy015 x y)),
          ((alphaDummy014 A B), (alphaDummy016 x y)),
          ((alphaDummy006 A B), (alphaDummy008 x y)),
          ((alphaDummy005 A B), (alphaDummy007 x y)),
          ((alphaDummy011 A B), (alphaDummy012 x y)),
          ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
          ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0001`. -/
@[expose]
noncomputable def splitAlpha0001 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((alphaDummy006 A B), (alphaDummy008 x y)),
        ((alphaDummy005 A B), (alphaDummy007 x y)),
        ((alphaDummy011 A B), (alphaDummy012 x y)),
        ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
        ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy006 A B)) (Class.cv (alphaDummy000 A B)))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy005 A B))
            (synCphi (Class.cv (alphaDummy006 A B))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy008 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy007 x y))
            (synCphi (Class.cv (alphaDummy008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A B) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A B) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0008 A B) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0009 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0005 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0007 x y) 0))
                (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_y
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy001 A B))).fv)
              (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (alphaDummy006 A B))).fv)
                      (by decide)) (freshVar_injective (((Class.cv (alphaDummy008 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A B) 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((alphaDummy021 A B), (alphaDummy024 x y)),
        ((alphaDummy020 A B), (alphaDummy023 x y)),
        ((alphaDummy019 A B), (alphaDummy022 x y)),
        ((alphaDummy017 A B), (alphaDummy018 x y)),
        ((alphaDummy013 A B), (alphaDummy015 x y)),
        ((alphaDummy014 A B), (alphaDummy016 x y)),
        ((alphaDummy006 A B), (alphaDummy008 x y)),
        ((alphaDummy005 A B), (alphaDummy007 x y)),
        ((alphaDummy011 A B), (alphaDummy012 x y)),
        ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
        ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0000 x y z A B))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy017 A B), (alphaDummy018 x y)),
                              ((alphaDummy013 A B), (alphaDummy015 x y)),
                              ((alphaDummy014 A B), (alphaDummy016 x y)),
                              ((alphaDummy006 A B), (alphaDummy008 x y)),
                              ((alphaDummy005 A B), (alphaDummy007 x y)),
                              ((alphaDummy011 A B), (alphaDummy012 x y)),
                              ((alphaDummy009 A B), (alphaDummy010 x y)),
                              ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
                              ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy017 A B), (alphaDummy018 x y)),
                              ((alphaDummy013 A B), (alphaDummy015 x y)),
                              ((alphaDummy014 A B), (alphaDummy016 x y)),
                              ((alphaDummy006 A B), (alphaDummy008 x y)),
                              ((alphaDummy005 A B), (alphaDummy007 x y)),
                              ((alphaDummy011 A B), (alphaDummy012 x y)),
                              ((alphaDummy009 A B), (alphaDummy010 x y)),
                              ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
                              ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0002`. -/
@[expose]
noncomputable def splitAlpha0002 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy021 A B), (alphaDummy024 x y)),
        ((alphaDummy020 A B), (alphaDummy023 x y)),
        ((alphaDummy019 A B), (alphaDummy022 x y)),
        ((alphaDummy017 A B), (alphaDummy018 x y)),
        ((alphaDummy013 A B), (alphaDummy015 x y)),
        ((alphaDummy014 A B), (alphaDummy016 x y)),
        ((alphaDummy039 A B), (alphaDummy040 x y)),
        ((alphaDummy037 A B), (alphaDummy038 x y)),
        ((alphaDummy006 A B), (alphaDummy008 x y)),
        ((alphaDummy005 A B), (alphaDummy007 x y)),
        ((alphaDummy035 A B), (alphaDummy036 x y)),
        ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
        ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy019 A B))
            (synCun (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy022 x y))
            (synCun (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy021 A B), (alphaDummy024 x y)),
          ((alphaDummy020 A B), (alphaDummy023 x y)),
          ((alphaDummy019 A B), (alphaDummy022 x y)),
          ((alphaDummy017 A B), (alphaDummy018 x y)),
          ((alphaDummy013 A B), (alphaDummy015 x y)),
          ((alphaDummy014 A B), (alphaDummy016 x y)),
          ((alphaDummy039 A B), (alphaDummy040 x y)),
          ((alphaDummy037 A B), (alphaDummy038 x y)),
          ((alphaDummy006 A B), (alphaDummy008 x y)),
          ((alphaDummy005 A B), (alphaDummy007 x y)),
          ((alphaDummy035 A B), (alphaDummy036 x y)),
          ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
          ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0003`. -/
@[expose]
noncomputable def splitAlpha0003 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy039 A B), (alphaDummy040 x y)),
        ((alphaDummy037 A B), (alphaDummy038 x y)),
        ((alphaDummy006 A B), (alphaDummy008 x y)),
        ((alphaDummy005 A B), (alphaDummy007 x y)),
        ((alphaDummy035 A B), (alphaDummy036 x y)),
        ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
        ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy039 A B))
          (synCphi (Class.cv (alphaDummy006 A B)))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy039 A B))
            (synCphi (Class.cv (alphaDummy006 A B))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy040 x y))
          (synCphi (Class.cv (alphaDummy008 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy040 x y))
            (synCphi (Class.cv (alphaDummy008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0040 A B) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0)) (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0038 A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (alphaDummy006 A B))).fv) (by decide))
                  (freshVar_injective (((Class.cv (alphaDummy008 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0014 A B) 1)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0015 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((alphaDummy021 A B), (alphaDummy024 x y)),
                                        ((alphaDummy020 A B), (alphaDummy023 x y)),
                                        ((alphaDummy019 A B), (alphaDummy022 x y)),
                                        ((alphaDummy017 A B), (alphaDummy018 x y)),
                                        ((alphaDummy013 A B), (alphaDummy015 x y)),
                                        ((alphaDummy014 A B), (alphaDummy016 x y)),
                                        ((alphaDummy039 A B), (alphaDummy040 x y)),
                                        ((alphaDummy037 A B), (alphaDummy038 x y)),
                                        ((alphaDummy006 A B), (alphaDummy008 x y)),
                                        ((alphaDummy005 A B), (alphaDummy007 x y)),
                                        ((alphaDummy035 A B), (alphaDummy036 x y)),
                                        ((alphaDummy009 A B), (alphaDummy010 x y)),
                                        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
                                        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                                      (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (splitAlpha0002 x y z A B))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((alphaDummy017 A B), (alphaDummy018 x y)),
                            ((alphaDummy013 A B), (alphaDummy015 x y)),
                            ((alphaDummy014 A B), (alphaDummy016 x y)),
                            ((alphaDummy039 A B), (alphaDummy040 x y)),
                            ((alphaDummy037 A B), (alphaDummy038 x y)),
                            ((alphaDummy006 A B), (alphaDummy008 x y)),
                            ((alphaDummy005 A B), (alphaDummy007 x y)),
                            ((alphaDummy035 A B), (alphaDummy036 x y)),
                            ((alphaDummy009 A B), (alphaDummy010 x y)),
                            ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
                            ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((alphaDummy017 A B), (alphaDummy018 x y)),
                            ((alphaDummy013 A B), (alphaDummy015 x y)),
                            ((alphaDummy014 A B), (alphaDummy016 x y)),
                            ((alphaDummy039 A B), (alphaDummy040 x y)),
                            ((alphaDummy037 A B), (alphaDummy038 x y)),
                            ((alphaDummy006 A B), (alphaDummy008 x y)),
                            ((alphaDummy005 A B), (alphaDummy007 x y)),
                            ((alphaDummy035 A B), (alphaDummy036 x y)),
                            ((alphaDummy009 A B), (alphaDummy010 x y)),
                            ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
                            ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1)) (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0040 A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0038 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (alphaDummy006 A B))).fv)
                      (by decide)) (freshVar_injective (((Class.cv (alphaDummy008 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A B) 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((alphaDummy021 A B), (alphaDummy024 x y)),
        ((alphaDummy020 A B), (alphaDummy023 x y)),
        ((alphaDummy019 A B), (alphaDummy022 x y)),
        ((alphaDummy017 A B), (alphaDummy018 x y)),
        ((alphaDummy013 A B), (alphaDummy015 x y)),
        ((alphaDummy014 A B), (alphaDummy016 x y)),
        ((alphaDummy039 A B), (alphaDummy040 x y)),
        ((alphaDummy037 A B), (alphaDummy038 x y)),
        ((alphaDummy006 A B), (alphaDummy008 x y)),
        ((alphaDummy005 A B), (alphaDummy007 x y)),
        ((alphaDummy035 A B), (alphaDummy036 x y)),
        ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
        ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0002 x y z A B))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy017 A B), (alphaDummy018 x y)),
                              ((alphaDummy013 A B), (alphaDummy015 x y)),
                              ((alphaDummy014 A B), (alphaDummy016 x y)),
                              ((alphaDummy039 A B), (alphaDummy040 x y)),
                              ((alphaDummy037 A B), (alphaDummy038 x y)),
                              ((alphaDummy006 A B), (alphaDummy008 x y)),
                              ((alphaDummy005 A B), (alphaDummy007 x y)),
                              ((alphaDummy035 A B), (alphaDummy036 x y)),
                              ((alphaDummy009 A B), (alphaDummy010 x y)),
                              ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
                              ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy017 A B), (alphaDummy018 x y)),
                              ((alphaDummy013 A B), (alphaDummy015 x y)),
                              ((alphaDummy014 A B), (alphaDummy016 x y)),
                              ((alphaDummy039 A B), (alphaDummy040 x y)),
                              ((alphaDummy037 A B), (alphaDummy038 x y)),
                              ((alphaDummy006 A B), (alphaDummy008 x y)),
                              ((alphaDummy005 A B), (alphaDummy007 x y)),
                              ((alphaDummy035 A B), (alphaDummy036 x y)),
                              ((alphaDummy009 A B), (alphaDummy010 x y)),
                              ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
                              ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0004`. -/
@[expose]
noncomputable def splitAlpha0004 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.classEq (Class.cv (alphaDummy003 A B))
        (synCop (Class.cv (alphaDummy000 A B)) (Class.cv (alphaDummy001 A B))))
      (Wff.classEq (Class.cv (alphaDummy004 x y z A B))
        (synCop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (TAlphaClass.cv
      (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0002 A B) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0003 x y z A B) 0)))
        (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0000 A B) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0001 x y z A B) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0001 x y z A B dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0001 x y z A B dv_x_y)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0032 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0034 x y) 0)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0036 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0033 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy000 A B))).fv ∪
                                    ((Class.cv (alphaDummy001 A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (splitAlpha0003 x y z A B)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((alphaDummy037 A B), (alphaDummy038 x y)),
                                        ((alphaDummy006 A B), (alphaDummy008 x y)),
                                        ((alphaDummy005 A B), (alphaDummy007 x y)),
                                        ((alphaDummy035 A B), (alphaDummy036 x y)),
                                        ((alphaDummy009 A B), (alphaDummy010 x y)),
                                        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
                                        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                                      (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0032 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0034 x y) 0)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0036 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0033 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy000 A B))).fv ∪
                                    ((Class.cv (alphaDummy001 A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (splitAlpha0003 x y z A B)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((alphaDummy037 A B), (alphaDummy038 x y)),
                                        ((alphaDummy006 A B), (alphaDummy008 x y)),
                                        ((alphaDummy005 A B), (alphaDummy007 x y)),
                                        ((alphaDummy035 A B), (alphaDummy036 x y)),
                                        ((alphaDummy009 A B), (alphaDummy010 x y)),
                                        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
                                        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                                      (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0005`. -/
@[expose]
noncomputable def splitAlpha0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy057 A B), (alphaDummy060 x z)),
        ((alphaDummy056 A B), (alphaDummy059 x z)),
        ((alphaDummy055 A B), (alphaDummy058 x z)),
        ((alphaDummy053 A B), (alphaDummy054 x z)),
        ((alphaDummy049 A B), (alphaDummy051 x z)),
        ((alphaDummy050 A B), (alphaDummy052 x z)),
        ((alphaDummy042 A B), (alphaDummy044 x z)),
        ((alphaDummy041 A B), (alphaDummy043 x z)),
        ((alphaDummy047 A B), (alphaDummy048 x z)),
        ((alphaDummy045 A B), (alphaDummy046 x z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy056 A B)) (Class.cv (alphaDummy057 A B))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy055 A B))
            (synCun (Class.cv (alphaDummy056 A B)) (Class.cv (alphaDummy057 A B))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy059 x z)) (Class.cv (alphaDummy060 x z))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy058 x z))
            (synCun (Class.cv (alphaDummy059 x z)) (Class.cv (alphaDummy060 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy057 A B), (alphaDummy060 x z)),
          ((alphaDummy056 A B), (alphaDummy059 x z)),
          ((alphaDummy055 A B), (alphaDummy058 x z)),
          ((alphaDummy053 A B), (alphaDummy054 x z)),
          ((alphaDummy049 A B), (alphaDummy051 x z)),
          ((alphaDummy050 A B), (alphaDummy052 x z)),
          ((alphaDummy042 A B), (alphaDummy044 x z)),
          ((alphaDummy041 A B), (alphaDummy043 x z)),
          ((alphaDummy047 A B), (alphaDummy048 x z)),
          ((alphaDummy045 A B), (alphaDummy046 x z)), ((alphaDummy002 A B), z),
          ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
          ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 x z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 x z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0006`. -/
@[expose]
noncomputable def splitAlpha0006 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) :
    TAlphaWff
      [((alphaDummy042 A B), (alphaDummy044 x z)),
        ((alphaDummy041 A B), (alphaDummy043 x z)),
        ((alphaDummy047 A B), (alphaDummy048 x z)),
        ((alphaDummy045 A B), (alphaDummy046 x z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy042 A B)) (Class.cv (alphaDummy000 A B)))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy041 A B))
            (synCphi (Class.cv (alphaDummy042 A B))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy044 x z)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy043 x z))
            (synCphi (Class.cv (alphaDummy044 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0042 A B) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 x z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0042 A B) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 x z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A B) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0047 x z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0043 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0045 x z) 0))
                (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_z
                  (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (alphaDummy000 A B))).fv ∪ ((Class.cv (alphaDummy002 A B))).fv)
              (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 x z) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 A B) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 x z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (alphaDummy042 A B))).fv)
                      (by decide)) (freshVar_injective (((Class.cv (alphaDummy044 x z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0052 A B) 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 x z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0052 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0053 x z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0050 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0051 x z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((alphaDummy057 A B), (alphaDummy060 x z)),
        ((alphaDummy056 A B), (alphaDummy059 x z)),
        ((alphaDummy055 A B), (alphaDummy058 x z)),
        ((alphaDummy053 A B), (alphaDummy054 x z)),
        ((alphaDummy049 A B), (alphaDummy051 x z)),
        ((alphaDummy050 A B), (alphaDummy052 x z)),
        ((alphaDummy042 A B), (alphaDummy044 x z)),
        ((alphaDummy041 A B), (alphaDummy043 x z)),
        ((alphaDummy047 A B), (alphaDummy048 x z)),
        ((alphaDummy045 A B), (alphaDummy046 x z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x), ((alphaDummy003 A B),
        (alphaDummy004 x y z A B))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0005 x y z A B))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy053 A B), (alphaDummy054 x z)),
                              ((alphaDummy049 A B), (alphaDummy051 x z)),
                              ((alphaDummy050 A B), (alphaDummy052 x z)),
                              ((alphaDummy042 A B), (alphaDummy044 x z)),
                              ((alphaDummy041 A B), (alphaDummy043 x z)),
                              ((alphaDummy047 A B), (alphaDummy048 x z)),
                              ((alphaDummy045 A B), (alphaDummy046 x z)),
                              ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                              ((alphaDummy000 A B), x),
                              ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy053 A B), (alphaDummy054 x z)),
                              ((alphaDummy049 A B), (alphaDummy051 x z)),
                              ((alphaDummy050 A B), (alphaDummy052 x z)),
                              ((alphaDummy042 A B), (alphaDummy044 x z)),
                              ((alphaDummy041 A B), (alphaDummy043 x z)),
                              ((alphaDummy047 A B), (alphaDummy048 x z)),
                              ((alphaDummy045 A B), (alphaDummy046 x z)),
                              ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                              ((alphaDummy000 A B), x),
                              ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0007`. -/
@[expose]
noncomputable def splitAlpha0007 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy057 A B), (alphaDummy060 x z)),
        ((alphaDummy056 A B), (alphaDummy059 x z)),
        ((alphaDummy055 A B), (alphaDummy058 x z)),
        ((alphaDummy053 A B), (alphaDummy054 x z)),
        ((alphaDummy049 A B), (alphaDummy051 x z)),
        ((alphaDummy050 A B), (alphaDummy052 x z)),
        ((alphaDummy075 A B), (alphaDummy076 x z)),
        ((alphaDummy073 A B), (alphaDummy074 x z)),
        ((alphaDummy042 A B), (alphaDummy044 x z)),
        ((alphaDummy041 A B), (alphaDummy043 x z)),
        ((alphaDummy071 A B), (alphaDummy072 x z)),
        ((alphaDummy045 A B), (alphaDummy046 x z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy056 A B)) (Class.cv (alphaDummy057 A B))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy055 A B))
            (synCun (Class.cv (alphaDummy056 A B)) (Class.cv (alphaDummy057 A B))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy059 x z)) (Class.cv (alphaDummy060 x z))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy058 x z))
            (synCun (Class.cv (alphaDummy059 x z)) (Class.cv (alphaDummy060 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy057 A B), (alphaDummy060 x z)),
          ((alphaDummy056 A B), (alphaDummy059 x z)),
          ((alphaDummy055 A B), (alphaDummy058 x z)),
          ((alphaDummy053 A B), (alphaDummy054 x z)),
          ((alphaDummy049 A B), (alphaDummy051 x z)),
          ((alphaDummy050 A B), (alphaDummy052 x z)),
          ((alphaDummy075 A B), (alphaDummy076 x z)),
          ((alphaDummy073 A B), (alphaDummy074 x z)),
          ((alphaDummy042 A B), (alphaDummy044 x z)),
          ((alphaDummy041 A B), (alphaDummy043 x z)),
          ((alphaDummy071 A B), (alphaDummy072 x z)),
          ((alphaDummy045 A B), (alphaDummy046 x z)), ((alphaDummy002 A B), z),
          ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
          ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy049 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy051 x z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 x z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 x z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0008`. -/
@[expose]
noncomputable def splitAlpha0008 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy075 A B), (alphaDummy076 x z)),
        ((alphaDummy073 A B), (alphaDummy074 x z)),
        ((alphaDummy042 A B), (alphaDummy044 x z)),
        ((alphaDummy041 A B), (alphaDummy043 x z)),
        ((alphaDummy071 A B), (alphaDummy072 x z)),
        ((alphaDummy045 A B), (alphaDummy046 x z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.classMem (Class.cv (alphaDummy075 A B))
        (synCphi (Class.cv (alphaDummy042 A B))))
      (Wff.classMem (Class.cv (alphaDummy076 x z))
        (synCphi (Class.cv (alphaDummy044 x z)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 x z) 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 A B) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 x z) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0078 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 x z) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 A B) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 x z) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (alphaDummy042 A B))).fv) (by decide))
                (freshVar_injective (((Class.cv (alphaDummy044 x z))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0052 A B) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0053 x z) 1)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 x z) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0050 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((alphaDummy057 A B), (alphaDummy060 x z)),
                                      ((alphaDummy056 A B), (alphaDummy059 x z)),
                                      ((alphaDummy055 A B), (alphaDummy058 x z)),
                                      ((alphaDummy053 A B), (alphaDummy054 x z)),
                                      ((alphaDummy049 A B), (alphaDummy051 x z)),
                                      ((alphaDummy050 A B), (alphaDummy052 x z)),
                                      ((alphaDummy075 A B), (alphaDummy076 x z)),
                                      ((alphaDummy073 A B), (alphaDummy074 x z)),
                                      ((alphaDummy042 A B), (alphaDummy044 x z)),
                                      ((alphaDummy041 A B), (alphaDummy043 x z)),
                                      ((alphaDummy071 A B), (alphaDummy072 x z)),
                                      ((alphaDummy045 A B), (alphaDummy046 x z)),
                                      ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                                      ((alphaDummy000 A B), x), ((alphaDummy003 A B),
                                        (alphaDummy004 x y z A B))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (splitAlpha0007 x y z A B))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((alphaDummy053 A B), (alphaDummy054 x z)),
                          ((alphaDummy049 A B), (alphaDummy051 x z)),
                          ((alphaDummy050 A B), (alphaDummy052 x z)),
                          ((alphaDummy075 A B), (alphaDummy076 x z)),
                          ((alphaDummy073 A B), (alphaDummy074 x z)),
                          ((alphaDummy042 A B), (alphaDummy044 x z)),
                          ((alphaDummy041 A B), (alphaDummy043 x z)),
                          ((alphaDummy071 A B), (alphaDummy072 x z)),
                          ((alphaDummy045 A B), (alphaDummy046 x z)),
                          ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                          ((alphaDummy000 A B), x),
                          ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((alphaDummy053 A B), (alphaDummy054 x z)),
                          ((alphaDummy049 A B), (alphaDummy051 x z)),
                          ((alphaDummy050 A B), (alphaDummy052 x z)),
                          ((alphaDummy075 A B), (alphaDummy076 x z)),
                          ((alphaDummy073 A B), (alphaDummy074 x z)),
                          ((alphaDummy042 A B), (alphaDummy044 x z)),
                          ((alphaDummy041 A B), (alphaDummy043 x z)),
                          ((alphaDummy071 A B), (alphaDummy072 x z)),
                          ((alphaDummy045 A B), (alphaDummy046 x z)),
                          ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                          ((alphaDummy000 A B), x),
                          ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Proof-translation construction identified upstream as `wpp_refl_0014`. -/
@[expose]
noncomputable def wppRefl0014 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) :
    TReflOn
      [((alphaDummy002 A B), z), ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (B).fv :=
  by
  intro u hu
  exact
    (TAlphaVar.there (fun h_eq => ((wpp_notmem_0202 A B)) (h_eq ▸ hu))
      (fun h_eq => ((wpp_notmem_0203 z B dv_B_z)) (h_eq ▸ hu))
      (TAlphaVar.there (fun h_eq => ((wpp_notmem_0200 A B)) (h_eq ▸ hu))
        (fun h_eq => ((wpp_notmem_0201 y B dv_B_y)) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => ((wpp_notmem_0198 A B)) (h_eq ▸ hu))
          (fun h_eq => ((wpp_notmem_0199 x B dv_B_x)) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => ((wpp_notmem_0196 A B)) (h_eq ▸ hu))
            (fun h_eq => ((wpp_notmem_0197 x y z A B dv_B_z)) (h_eq ▸ hu))
            (TAlphaVar.free (by simp) (by simp))))))

/-- Proof-translation construction identified upstream as `split_alpha_0009`. -/
@[expose]
noncomputable def splitAlpha0009 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) :
    TAlphaWff
      [((alphaDummy002 A B), z), ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.classMem
        (synCop (Class.cv (alphaDummy000 A B)) (Class.cv (alphaDummy002 A B))) B)
      (Wff.classMem (synCop (Class.cv x) (Class.cv z)) B) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (splitAlpha0006 x y z A B dv_x_y dv_x_z)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (splitAlpha0006 x y z A B dv_x_y dv_x_z)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 x z) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0070 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0072 x z) 0)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 x z) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0071 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 x z) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy000 A B))).fv ∪
                                    ((Class.cv (alphaDummy002 A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.conj (splitAlpha0008 x y z A B)
        (splitAlpha0008 x y z A B))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((alphaDummy073 A B), (alphaDummy074 x z)),
                                        ((alphaDummy042 A B), (alphaDummy044 x z)),
                                        ((alphaDummy041 A B), (alphaDummy043 x z)),
                                        ((alphaDummy071 A B), (alphaDummy072 x z)),
                                        ((alphaDummy045 A B), (alphaDummy046 x z)),
                                        ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                                        ((alphaDummy000 A B), x), ((alphaDummy003 A B),
        (alphaDummy004 x y z A B))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 x z) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0070 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0072 x z) 0)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 x z) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0071 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 x z) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy000 A B))).fv ∪
                                    ((Class.cv (alphaDummy002 A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.conj (splitAlpha0008 x y z A B)
        (splitAlpha0008 x y z A B))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((alphaDummy073 A B), (alphaDummy074 x z)),
                                        ((alphaDummy042 A B), (alphaDummy044 x z)),
                                        ((alphaDummy041 A B), (alphaDummy043 x z)),
                                        ((alphaDummy071 A B), (alphaDummy072 x z)),
                                        ((alphaDummy045 A B), (alphaDummy046 x z)),
                                        ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                                        ((alphaDummy000 A B), x), ((alphaDummy003 A B),
        (alphaDummy004 x y z A B))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c]))))))))))))))))))
    (TAlphaClass.reflOfReflOn
      [((alphaDummy002 A B), z), ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      B (wppRefl0014 x y z A B dv_B_x dv_B_y dv_B_z)))

/-- Proof-translation construction identified upstream as `split_alpha_0010`. -/
@[expose]
noncomputable def splitAlpha0010 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy093 A B), (alphaDummy096 y z)),
        ((alphaDummy092 A B), (alphaDummy095 y z)),
        ((alphaDummy091 A B), (alphaDummy094 y z)),
        ((alphaDummy089 A B), (alphaDummy090 y z)),
        ((alphaDummy085 A B), (alphaDummy087 y z)),
        ((alphaDummy086 A B), (alphaDummy088 y z)),
        ((alphaDummy078 A B), (alphaDummy080 y z)),
        ((alphaDummy077 A B), (alphaDummy079 y z)),
        ((alphaDummy083 A B), (alphaDummy084 y z)),
        ((alphaDummy081 A B), (alphaDummy082 y z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy092 A B)) (Class.cv (alphaDummy093 A B))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy091 A B))
            (synCun (Class.cv (alphaDummy092 A B)) (Class.cv (alphaDummy093 A B))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy095 y z)) (Class.cv (alphaDummy096 y z))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy094 y z))
            (synCun (Class.cv (alphaDummy095 y z)) (Class.cv (alphaDummy096 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0094 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0092 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0098 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0096 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0094 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0092 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0098 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0096 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy093 A B), (alphaDummy096 y z)),
          ((alphaDummy092 A B), (alphaDummy095 y z)),
          ((alphaDummy091 A B), (alphaDummy094 y z)),
          ((alphaDummy089 A B), (alphaDummy090 y z)),
          ((alphaDummy085 A B), (alphaDummy087 y z)),
          ((alphaDummy086 A B), (alphaDummy088 y z)),
          ((alphaDummy078 A B), (alphaDummy080 y z)),
          ((alphaDummy077 A B), (alphaDummy079 y z)),
          ((alphaDummy083 A B), (alphaDummy084 y z)),
          ((alphaDummy081 A B), (alphaDummy082 y z)), ((alphaDummy002 A B), z),
          ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
          ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0102 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0100 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0102 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0100 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0106 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0104 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0106 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0104 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0011`. -/
@[expose]
noncomputable def splitAlpha0011 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy078 A B), (alphaDummy080 y z)),
        ((alphaDummy077 A B), (alphaDummy079 y z)),
        ((alphaDummy083 A B), (alphaDummy084 y z)),
        ((alphaDummy081 A B), (alphaDummy082 y z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy078 A B)) (Class.cv (alphaDummy002 A B)))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy077 A B))
            (synCphi (Class.cv (alphaDummy078 A B))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy080 y z)) (Class.cv z)) (Wff.neg
          (Wff.classEq (Class.cv (alphaDummy079 y z))
            (synCphi (Class.cv (alphaDummy080 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A B) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 y z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A B) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 y z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0084 A B) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0085 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0081 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0083 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (alphaDummy002 A B))).fv ∪
                ((Class.cv (alphaDummy001 A B))).fv) (by decide))
            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0086 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 y z) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0086 A B) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (alphaDummy078 A B))).fv)
                      (by decide)) (freshVar_injective (((Class.cv (alphaDummy080 y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0090 A B) 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0090 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0091 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0088 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((alphaDummy093 A B), (alphaDummy096 y z)),
        ((alphaDummy092 A B), (alphaDummy095 y z)),
        ((alphaDummy091 A B), (alphaDummy094 y z)),
        ((alphaDummy089 A B), (alphaDummy090 y z)),
        ((alphaDummy085 A B), (alphaDummy087 y z)),
        ((alphaDummy086 A B), (alphaDummy088 y z)),
        ((alphaDummy078 A B), (alphaDummy080 y z)),
        ((alphaDummy077 A B), (alphaDummy079 y z)),
        ((alphaDummy083 A B), (alphaDummy084 y z)),
        ((alphaDummy081 A B), (alphaDummy082 y z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x), ((alphaDummy003 A B),
        (alphaDummy004 x y z A B))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (splitAlpha0010 x y z A B))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy089 A B), (alphaDummy090 y z)),
                              ((alphaDummy085 A B), (alphaDummy087 y z)),
                              ((alphaDummy086 A B), (alphaDummy088 y z)),
                              ((alphaDummy078 A B), (alphaDummy080 y z)),
                              ((alphaDummy077 A B), (alphaDummy079 y z)),
                              ((alphaDummy083 A B), (alphaDummy084 y z)),
                              ((alphaDummy081 A B), (alphaDummy082 y z)),
                              ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                              ((alphaDummy000 A B), x),
                              ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((alphaDummy089 A B), (alphaDummy090 y z)),
                              ((alphaDummy085 A B), (alphaDummy087 y z)),
                              ((alphaDummy086 A B), (alphaDummy088 y z)),
                              ((alphaDummy078 A B), (alphaDummy080 y z)),
                              ((alphaDummy077 A B), (alphaDummy079 y z)),
                              ((alphaDummy083 A B), (alphaDummy084 y z)),
                              ((alphaDummy081 A B), (alphaDummy082 y z)),
                              ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                              ((alphaDummy000 A B), x),
                              ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0012`. -/
@[expose]
noncomputable def splitAlpha0012 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy093 A B), (alphaDummy096 y z)),
        ((alphaDummy092 A B), (alphaDummy095 y z)),
        ((alphaDummy091 A B), (alphaDummy094 y z)),
        ((alphaDummy089 A B), (alphaDummy090 y z)),
        ((alphaDummy085 A B), (alphaDummy087 y z)),
        ((alphaDummy086 A B), (alphaDummy088 y z)),
        ((alphaDummy111 A B), (alphaDummy112 y z)),
        ((alphaDummy109 A B), (alphaDummy110 y z)),
        ((alphaDummy078 A B), (alphaDummy080 y z)),
        ((alphaDummy077 A B), (alphaDummy079 y z)),
        ((alphaDummy107 A B), (alphaDummy108 y z)),
        ((alphaDummy081 A B), (alphaDummy082 y z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy092 A B)) (Class.cv (alphaDummy093 A B))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy091 A B))
            (synCun (Class.cv (alphaDummy092 A B)) (Class.cv (alphaDummy093 A B))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy095 y z)) (Class.cv (alphaDummy096 y z))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy094 y z))
            (synCun (Class.cv (alphaDummy095 y z)) (Class.cv (alphaDummy096 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0094 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0092 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0098 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0096 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0094 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0092 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0098 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0096 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy093 A B), (alphaDummy096 y z)),
          ((alphaDummy092 A B), (alphaDummy095 y z)),
          ((alphaDummy091 A B), (alphaDummy094 y z)),
          ((alphaDummy089 A B), (alphaDummy090 y z)),
          ((alphaDummy085 A B), (alphaDummy087 y z)),
          ((alphaDummy086 A B), (alphaDummy088 y z)),
          ((alphaDummy111 A B), (alphaDummy112 y z)),
          ((alphaDummy109 A B), (alphaDummy110 y z)),
          ((alphaDummy078 A B), (alphaDummy080 y z)),
          ((alphaDummy077 A B), (alphaDummy079 y z)),
          ((alphaDummy107 A B), (alphaDummy108 y z)),
          ((alphaDummy081 A B), (alphaDummy082 y z)), ((alphaDummy002 A B), z),
          ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
          ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0102 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0100 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0102 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0100 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy085 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy087 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0106 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0104 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0106 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0104 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0013`. -/
@[expose]
noncomputable def splitAlpha0013 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy111 A B), (alphaDummy112 y z)),
        ((alphaDummy109 A B), (alphaDummy110 y z)),
        ((alphaDummy078 A B), (alphaDummy080 y z)),
        ((alphaDummy077 A B), (alphaDummy079 y z)),
        ((alphaDummy107 A B), (alphaDummy108 y z)),
        ((alphaDummy081 A B), (alphaDummy082 y z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.classMem (Class.cv (alphaDummy111 A B))
        (synCphi (Class.cv (alphaDummy078 A B))))
      (Wff.classMem (Class.cv (alphaDummy112 y z))
        (synCphi (Class.cv (alphaDummy080 y z)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0086 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 y z) 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0086 A B) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 y z) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0116 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0117 y z) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0114 A B) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0115 y z) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (alphaDummy078 A B))).fv) (by decide))
                (freshVar_injective (((Class.cv (alphaDummy080 y z))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0090 A B) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0091 y z) 1)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0090 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 y z) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0088 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((alphaDummy093 A B), (alphaDummy096 y z)),
                                      ((alphaDummy092 A B), (alphaDummy095 y z)),
                                      ((alphaDummy091 A B), (alphaDummy094 y z)),
                                      ((alphaDummy089 A B), (alphaDummy090 y z)),
                                      ((alphaDummy085 A B), (alphaDummy087 y z)),
                                      ((alphaDummy086 A B), (alphaDummy088 y z)),
                                      ((alphaDummy111 A B), (alphaDummy112 y z)),
                                      ((alphaDummy109 A B), (alphaDummy110 y z)),
                                      ((alphaDummy078 A B), (alphaDummy080 y z)),
                                      ((alphaDummy077 A B), (alphaDummy079 y z)),
                                      ((alphaDummy107 A B), (alphaDummy108 y z)),
                                      ((alphaDummy081 A B), (alphaDummy082 y z)),
                                      ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                                      ((alphaDummy000 A B), x), ((alphaDummy003 A B),
                                        (alphaDummy004 x y z A B))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (splitAlpha0012 x y z A B))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((alphaDummy089 A B), (alphaDummy090 y z)),
                          ((alphaDummy085 A B), (alphaDummy087 y z)),
                          ((alphaDummy086 A B), (alphaDummy088 y z)),
                          ((alphaDummy111 A B), (alphaDummy112 y z)),
                          ((alphaDummy109 A B), (alphaDummy110 y z)),
                          ((alphaDummy078 A B), (alphaDummy080 y z)),
                          ((alphaDummy077 A B), (alphaDummy079 y z)),
                          ((alphaDummy107 A B), (alphaDummy108 y z)),
                          ((alphaDummy081 A B), (alphaDummy082 y z)),
                          ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                          ((alphaDummy000 A B), x),
                          ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((alphaDummy089 A B), (alphaDummy090 y z)),
                          ((alphaDummy085 A B), (alphaDummy087 y z)),
                          ((alphaDummy086 A B), (alphaDummy088 y z)),
                          ((alphaDummy111 A B), (alphaDummy112 y z)),
                          ((alphaDummy109 A B), (alphaDummy110 y z)),
                          ((alphaDummy078 A B), (alphaDummy080 y z)),
                          ((alphaDummy077 A B), (alphaDummy079 y z)),
                          ((alphaDummy107 A B), (alphaDummy108 y z)),
                          ((alphaDummy081 A B), (alphaDummy082 y z)),
                          ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                          ((alphaDummy000 A B), x),
                          ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0014`. -/
@[expose]
noncomputable def splitAlpha0014 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_y_z : y ≠ z) :
    TAlphaWff
      [((alphaDummy081 A B), (alphaDummy082 y z)), ((alphaDummy002 A B), z),
        ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy081 A B)) (synCcompl
            (Class.cab (alphaDummy077 A B)
              (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy002 A B))
                (Wff.classEq (Class.cv (alphaDummy077 A B))
                  (synCphi (Class.cv (alphaDummy078 A B)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy081 A B)) (synCcompl
              (Class.cab (alphaDummy077 A B)
                (synWrex (alphaDummy078 A B) (Class.cv (alphaDummy001 A B))
                  (Wff.classEq (Class.cv (alphaDummy077 A B))
                    (synCun (synCphi (Class.cv (alphaDummy078 A B)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy082 y z)) (synCcompl
            (Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy079 y z))
                  (synCphi (Class.cv (alphaDummy080 y z)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy082 y z)) (synCcompl
              (Class.cab (alphaDummy079 y z) (synWrex (alphaDummy080 y z) (Class.cv y)
                  (Wff.classEq (Class.cv (alphaDummy079 y z))
                    (synCun (synCphi (Class.cv (alphaDummy080 y z)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0011 x y z A B)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0011 x y z A B))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0112 A B) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0113 y z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0109 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0111 y z) 0)) (TAlphaVar.there
                                    (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alphaDummy002 A B))).fv ∪
                                ((Class.cv (alphaDummy001 A B))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (splitAlpha0013 x y z A B)
                                      (splitAlpha0013 x y z A B)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((alphaDummy109 A B), (alphaDummy110 y z)),
                                    ((alphaDummy078 A B), (alphaDummy080 y z)),
                                    ((alphaDummy077 A B), (alphaDummy079 y z)),
                                    ((alphaDummy107 A B), (alphaDummy108 y z)),
                                    ((alphaDummy081 A B), (alphaDummy082 y z)),
                                    ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                                    ((alphaDummy000 A B), x),
                                    ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0112 A B) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0113 y z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0109 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0111 y z) 0)) (TAlphaVar.there
                                    (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alphaDummy002 A B))).fv ∪
                                ((Class.cv (alphaDummy001 A B))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (splitAlpha0013 x y z A B)
                                      (splitAlpha0013 x y z A B)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((alphaDummy109 A B), (alphaDummy110 y z)),
                                    ((alphaDummy078 A B), (alphaDummy080 y z)),
                                    ((alphaDummy077 A B), (alphaDummy079 y z)),
                                    ((alphaDummy107 A B), (alphaDummy108 y z)),
                                    ((alphaDummy081 A B), (alphaDummy082 y z)),
                                    ((alphaDummy002 A B), z), ((alphaDummy001 A B), y),
                                    ((alphaDummy000 A B), x),
                                    ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

/-- Proof-translation construction identified upstream as `wpp_refl_0022`. -/
@[expose]
noncomputable def wppRefl0022 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) :
    TReflOn
      [((alphaDummy002 A B), z), ((alphaDummy001 A B), y), ((alphaDummy000 A B), x),
        ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (A).fv :=
  by
  intro u hu
  exact
    (TAlphaVar.there (fun h_eq => ((wpp_notmem_0292 A B)) (h_eq ▸ hu))
      (fun h_eq => ((wpp_notmem_0293 z A dv_A_z)) (h_eq ▸ hu))
      (TAlphaVar.there (fun h_eq => ((wpp_notmem_0290 A B)) (h_eq ▸ hu))
        (fun h_eq => ((wpp_notmem_0291 y A dv_A_y)) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => ((wpp_notmem_0288 A B)) (h_eq ▸ hu))
          (fun h_eq => ((wpp_notmem_0289 x A dv_A_x)) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => ((wpp_notmem_0286 A B)) (h_eq ▸ hu))
            (fun h_eq => ((wpp_notmem_0287 x y z A B dv_A_z)) (h_eq ▸ hu))
            (TAlphaVar.free (by simp) (by simp))))))

end CompositionAlpha

/-- Checked nominal proof certificate identified upstream as `nominal_df_co`. -/
@[expose]
noncomputable def nominalDfCo (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCcom A B) (synCopab x y (synWex z
            (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (CompositionAlpha.splitAlpha0004 x y z A B dv_x_y) (TAlphaWff.ex
                (TAlphaWff.conj
                  (CompositionAlpha.splitAlpha0009 x y z A B dv_B_x dv_B_y dv_B_z dv_x_y
                    dv_x_z) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                          (CompositionAlpha.splitAlpha0014 x y z A B dv_y_z))))
                    (TAlphaClass.reflOfReflOn [((CompositionAlpha.alphaDummy002 A B), z),
                        ((CompositionAlpha.alphaDummy001 A B), y),
                        ((CompositionAlpha.alphaDummy000 A B), x),
                        ((CompositionAlpha.alphaDummy003 A B),
                          (CompositionAlpha.alphaDummy004 x y z A B))] A
                      (CompositionAlpha.wppRefl0022 x y z A B dv_A_x dv_A_y dv_A_z)))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
