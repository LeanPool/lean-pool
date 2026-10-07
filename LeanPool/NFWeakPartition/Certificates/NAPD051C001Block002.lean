/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAPD051C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAPD051C001Part010`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb051_split_alpha_0000`. -/
@[expose]
noncomputable def nb051SplitAlpha0000 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) :
    TAlphaWff
      [((nb051AlphaDummy019 x y A B C), (nb051AlphaDummy022 x y z)),
        ((nb051AlphaDummy018 x y A B C), (nb051AlphaDummy021 x y z)),
        ((nb051AlphaDummy017 x y A B C), (nb051AlphaDummy020 x y z)),
        ((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
        ((nb051AlphaDummy011 x y A B C), (nb051AlphaDummy013 x y z)),
        ((nb051AlphaDummy012 x y A B C), (nb051AlphaDummy014 x y z)),
        ((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
        ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
        ((nb051AlphaDummy009 x y A B C), (nb051AlphaDummy010 x y z)),
        ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
        ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb051AlphaDummy017 x y A B C))
            (synCun (Class.cv (nb051AlphaDummy018 x y A B C))
              (Class.cv (nb051AlphaDummy019 x y A B C))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb051AlphaDummy020 x y z))
            (synCun (Class.cv (nb051AlphaDummy021 x y z))
              (Class.cv (nb051AlphaDummy022 x y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0028 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0029 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0026 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0027 x y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0032 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0033 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0030 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0031 x y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0028 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0029 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0026 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0027 x y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0032 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0033 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0030 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0031 x y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb051AlphaDummy019 x y A B C), (nb051AlphaDummy022 x y z)),
          ((nb051AlphaDummy018 x y A B C), (nb051AlphaDummy021 x y z)),
          ((nb051AlphaDummy017 x y A B C), (nb051AlphaDummy020 x y z)),
          ((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
          ((nb051AlphaDummy011 x y A B C), (nb051AlphaDummy013 x y z)),
          ((nb051AlphaDummy012 x y A B C), (nb051AlphaDummy014 x y z)),
          ((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
          ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
          ((nb051AlphaDummy009 x y A B C), (nb051AlphaDummy010 x y z)),
          ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
          ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
          ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv)
                (by decide)) (freshVar_injective
                (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0036 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0037 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0034 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0035 x y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪
                                    ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0036 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0037 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0034 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0035 x y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪
                                    ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0040 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0041 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0038 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0039 x y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0040 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0041 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0038 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0039 x y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part013`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb051_split_alpha_0001`. -/
@[expose]
noncomputable def nb051SplitAlpha0001 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
        ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
        ((nb051AlphaDummy009 x y A B C), (nb051AlphaDummy010 x y z)),
        ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
        ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      (Wff.imp (Wff.classMem (Class.cv (nb051AlphaDummy004 x y A B C))
          (synCop (Class.cv x) (Class.cv y))) (Wff.neg
          (Wff.classEq (Class.cv (nb051AlphaDummy003 x y A B C))
            (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))
      (Wff.imp (Wff.classMem (Class.cv (nb051AlphaDummy006 x y z))
          (synCop (Class.cv x) (Class.cv y))) (Wff.neg
          (Wff.classEq (Class.cv (nb051AlphaDummy005 x y z))
            (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
      (TAlphaClass.reflOfReflOn
        [((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
          ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
          ((nb051AlphaDummy009 x y A B C), (nb051AlphaDummy010 x y z)),
          ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
          ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
          ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
        (synCop (Class.cv x) (Class.cv y)) (nb051WppRefl0000 x y z A B C dv_x_z dv_y_z)))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((synCop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb051AlphaDummy000 x y A B C))).fv) (by decide))
            (freshVar_injective
              (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt
                        (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb051AlphaDummy006 x y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0023 x y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb051AlphaDummy019 x y A B C),
        (nb051AlphaDummy022 x y z)), ((nb051AlphaDummy018 x y A B C),
        (nb051AlphaDummy021 x y z)), ((nb051AlphaDummy017 x y A B C),
        (nb051AlphaDummy020 x y z)), ((nb051AlphaDummy015 x y A B C),
        (nb051AlphaDummy016 x y z)), ((nb051AlphaDummy011 x y A B C),
        (nb051AlphaDummy013 x y z)), ((nb051AlphaDummy012 x y A B C),
        (nb051AlphaDummy014 x y z)), ((nb051AlphaDummy004 x y A B C),
        (nb051AlphaDummy006 x y z)), ((nb051AlphaDummy003 x y A B C),
        (nb051AlphaDummy005 x y z)), ((nb051AlphaDummy009 x y A B C),
        (nb051AlphaDummy010 x y z)), ((nb051AlphaDummy007 x y A B C),
        (nb051AlphaDummy008 x y z)), ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg
                                      (nb051SplitAlpha0000 x y z A B C))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
                              ((nb051AlphaDummy011 x y A B C),
                                (nb051AlphaDummy013 x y z)),
                              ((nb051AlphaDummy012 x y A B C),
                                (nb051AlphaDummy014 x y z)),
                              ((nb051AlphaDummy004 x y A B C),
                                (nb051AlphaDummy006 x y z)),
                              ((nb051AlphaDummy003 x y A B C),
                                (nb051AlphaDummy005 x y z)),
                              ((nb051AlphaDummy009 x y A B C),
                                (nb051AlphaDummy010 x y z)),
                              ((nb051AlphaDummy007 x y A B C),
                                (nb051AlphaDummy008 x y z)),
                              ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                              ((nb051AlphaDummy001 x y A B C),
                                (nb051AlphaDummy002 x y z A B C))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
                              ((nb051AlphaDummy011 x y A B C),
                                (nb051AlphaDummy013 x y z)),
                              ((nb051AlphaDummy012 x y A B C),
                                (nb051AlphaDummy014 x y z)),
                              ((nb051AlphaDummy004 x y A B C),
                                (nb051AlphaDummy006 x y z)),
                              ((nb051AlphaDummy003 x y A B C),
                                (nb051AlphaDummy005 x y z)),
                              ((nb051AlphaDummy009 x y A B C),
                                (nb051AlphaDummy010 x y z)),
                              ((nb051AlphaDummy007 x y A B C),
                                (nb051AlphaDummy008 x y z)),
                              ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                              ((nb051AlphaDummy001 x y A B C),
                                (nb051AlphaDummy002 x y z A B C))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part018`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb051_split_alpha_0002`. -/
@[expose]
noncomputable def nb051SplitAlpha0002 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) :
    TAlphaWff
      [((nb051AlphaDummy019 x y A B C), (nb051AlphaDummy022 x y z)),
        ((nb051AlphaDummy018 x y A B C), (nb051AlphaDummy021 x y z)),
        ((nb051AlphaDummy017 x y A B C), (nb051AlphaDummy020 x y z)),
        ((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
        ((nb051AlphaDummy011 x y A B C), (nb051AlphaDummy013 x y z)),
        ((nb051AlphaDummy012 x y A B C), (nb051AlphaDummy014 x y z)),
        ((nb051AlphaDummy037 x y A B C), (nb051AlphaDummy038 x y z)),
        ((nb051AlphaDummy035 x y A B C), (nb051AlphaDummy036 x y z)),
        ((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
        ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
        ((nb051AlphaDummy033 x y A B C), (nb051AlphaDummy034 x y z)),
        ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
        ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb051AlphaDummy018 x y A B C))
            (Class.cv (nb051AlphaDummy019 x y A B C))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb051AlphaDummy017 x y A B C))
            (synCun (Class.cv (nb051AlphaDummy018 x y A B C))
              (Class.cv (nb051AlphaDummy019 x y A B C))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb051AlphaDummy021 x y z))
            (Class.cv (nb051AlphaDummy022 x y z))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb051AlphaDummy020 x y z))
            (synCun (Class.cv (nb051AlphaDummy021 x y z))
              (Class.cv (nb051AlphaDummy022 x y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0028 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0029 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0026 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0027 x y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0032 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0033 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0030 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0031 x y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0028 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0029 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0026 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0027 x y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0032 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0033 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0030 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0031 x y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb051AlphaDummy019 x y A B C), (nb051AlphaDummy022 x y z)),
          ((nb051AlphaDummy018 x y A B C), (nb051AlphaDummy021 x y z)),
          ((nb051AlphaDummy017 x y A B C), (nb051AlphaDummy020 x y z)),
          ((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
          ((nb051AlphaDummy011 x y A B C), (nb051AlphaDummy013 x y z)),
          ((nb051AlphaDummy012 x y A B C), (nb051AlphaDummy014 x y z)),
          ((nb051AlphaDummy037 x y A B C), (nb051AlphaDummy038 x y z)),
          ((nb051AlphaDummy035 x y A B C), (nb051AlphaDummy036 x y z)),
          ((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
          ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
          ((nb051AlphaDummy033 x y A B C), (nb051AlphaDummy034 x y z)),
          ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
          ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
          ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪ ((synC1c)).fv)
                (by decide)) (freshVar_injective
                (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0036 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0037 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0034 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0035 x y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪
                                    ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0036 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0037 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0034 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0035 x y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb051AlphaDummy011 x y A B C))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb051AlphaDummy013 x y z))).fv ∪
                                    ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0040 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0041 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0038 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0039 x y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0040 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0041 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0038 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0039 x y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part021`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb051_split_alpha_0003`. -/
@[expose]
noncomputable def nb051SplitAlpha0003 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) :
    TAlphaWff
      [((nb051AlphaDummy037 x y A B C), (nb051AlphaDummy038 x y z)),
        ((nb051AlphaDummy035 x y A B C), (nb051AlphaDummy036 x y z)),
        ((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
        ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
        ((nb051AlphaDummy033 x y A B C), (nb051AlphaDummy034 x y z)),
        ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
        ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      (Wff.imp (Wff.classMem (Class.cv (nb051AlphaDummy037 x y A B C))
          (synCphi (Class.cv (nb051AlphaDummy004 x y A B C)))) (Wff.neg
          (Wff.classMem (Class.cv (nb051AlphaDummy037 x y A B C))
            (synCphi (Class.cv (nb051AlphaDummy004 x y A B C))))))
      (Wff.imp (Wff.classMem (Class.cv (nb051AlphaDummy038 x y z))
          (synCphi (Class.cv (nb051AlphaDummy006 x y z)))) (Wff.neg
          (Wff.classMem (Class.cv (nb051AlphaDummy038 x y z))
            (synCphi (Class.cv (nb051AlphaDummy006 x y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 0))
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 1))
                    (TAlphaVar.there (Nat.ne_of_lt
                        (mem_lt_freshVar (nb051_support_mem_0050 x y A B C) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0051 x y z) 0))
                      (TAlphaVar.there (Nat.ne_of_lt
                          (mem_lt_freshVar (nb051_support_mem_0048 x y A B C) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0049 x y z) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb051AlphaDummy004 x y A B C))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb051AlphaDummy006 x y z))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb051_support_mem_0024 x y A B C) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb051_support_mem_0025 x y z) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 0)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0022 x y A B C) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb051AlphaDummy019 x y A B C),
        (nb051AlphaDummy022 x y z)), ((nb051AlphaDummy018 x y A B C),
        (nb051AlphaDummy021 x y z)), ((nb051AlphaDummy017 x y A B C),
        (nb051AlphaDummy020 x y z)), ((nb051AlphaDummy015 x y A B C),
        (nb051AlphaDummy016 x y z)), ((nb051AlphaDummy011 x y A B C),
        (nb051AlphaDummy013 x y z)), ((nb051AlphaDummy012 x y A B C),
        (nb051AlphaDummy014 x y z)), ((nb051AlphaDummy037 x y A B C),
        (nb051AlphaDummy038 x y z)), ((nb051AlphaDummy035 x y A B C),
        (nb051AlphaDummy036 x y z)), ((nb051AlphaDummy004 x y A B C),
        (nb051AlphaDummy006 x y z)), ((nb051AlphaDummy003 x y A B C),
        (nb051AlphaDummy005 x y z)), ((nb051AlphaDummy033 x y A B C),
        (nb051AlphaDummy034 x y z)), ((nb051AlphaDummy007 x y A B C),
        (nb051AlphaDummy008 x y z)), ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                                        ((nb051AlphaDummy001 x y A B C),
        (nb051AlphaDummy002 x y z A B C))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb051SplitAlpha0002 x y z A B C))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
                            ((nb051AlphaDummy011 x y A B C), (nb051AlphaDummy013 x y z)),
                            ((nb051AlphaDummy012 x y A B C), (nb051AlphaDummy014 x y z)),
                            ((nb051AlphaDummy037 x y A B C), (nb051AlphaDummy038 x y z)),
                            ((nb051AlphaDummy035 x y A B C), (nb051AlphaDummy036 x y z)),
                            ((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
                            ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
                            ((nb051AlphaDummy033 x y A B C), (nb051AlphaDummy034 x y z)),
                            ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
                            ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                            ((nb051AlphaDummy001 x y A B C),
                              (nb051AlphaDummy002 x y z A B C))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
                            ((nb051AlphaDummy011 x y A B C), (nb051AlphaDummy013 x y z)),
                            ((nb051AlphaDummy012 x y A B C), (nb051AlphaDummy014 x y z)),
                            ((nb051AlphaDummy037 x y A B C), (nb051AlphaDummy038 x y z)),
                            ((nb051AlphaDummy035 x y A B C), (nb051AlphaDummy036 x y z)),
                            ((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
                            ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
                            ((nb051AlphaDummy033 x y A B C), (nb051AlphaDummy034 x y z)),
                            ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
                            ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                            ((nb051AlphaDummy001 x y A B C),
                              (nb051AlphaDummy002 x y z A B C))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt
                        (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 1))
                      (TAlphaVar.there (Nat.ne_of_lt
                          (mem_lt_freshVar (nb051_support_mem_0050 x y A B C) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0051 x y z) 0))
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0048 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0049 x y z) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb051AlphaDummy004 x y A B C))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb051AlphaDummy006 x y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0023 x y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb051AlphaDummy019 x y A B C),
        (nb051AlphaDummy022 x y z)), ((nb051AlphaDummy018 x y A B C),
        (nb051AlphaDummy021 x y z)), ((nb051AlphaDummy017 x y A B C),
        (nb051AlphaDummy020 x y z)), ((nb051AlphaDummy015 x y A B C),
        (nb051AlphaDummy016 x y z)), ((nb051AlphaDummy011 x y A B C),
        (nb051AlphaDummy013 x y z)), ((nb051AlphaDummy012 x y A B C),
        (nb051AlphaDummy014 x y z)), ((nb051AlphaDummy037 x y A B C),
        (nb051AlphaDummy038 x y z)), ((nb051AlphaDummy035 x y A B C),
        (nb051AlphaDummy036 x y z)), ((nb051AlphaDummy004 x y A B C),
        (nb051AlphaDummy006 x y z)), ((nb051AlphaDummy003 x y A B C),
        (nb051AlphaDummy005 x y z)), ((nb051AlphaDummy033 x y A B C),
        (nb051AlphaDummy034 x y z)), ((nb051AlphaDummy007 x y A B C),
        (nb051AlphaDummy008 x y z)), ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg
                                      (nb051SplitAlpha0002 x y z A B C))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
                              ((nb051AlphaDummy011 x y A B C),
                                (nb051AlphaDummy013 x y z)),
                              ((nb051AlphaDummy012 x y A B C),
                                (nb051AlphaDummy014 x y z)),
                              ((nb051AlphaDummy037 x y A B C),
                                (nb051AlphaDummy038 x y z)),
                              ((nb051AlphaDummy035 x y A B C),
                                (nb051AlphaDummy036 x y z)),
                              ((nb051AlphaDummy004 x y A B C),
                                (nb051AlphaDummy006 x y z)),
                              ((nb051AlphaDummy003 x y A B C),
                                (nb051AlphaDummy005 x y z)),
                              ((nb051AlphaDummy033 x y A B C),
                                (nb051AlphaDummy034 x y z)),
                              ((nb051AlphaDummy007 x y A B C),
                                (nb051AlphaDummy008 x y z)),
                              ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                              ((nb051AlphaDummy001 x y A B C),
                                (nb051AlphaDummy002 x y z A B C))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb051AlphaDummy015 x y A B C), (nb051AlphaDummy016 x y z)),
                              ((nb051AlphaDummy011 x y A B C),
                                (nb051AlphaDummy013 x y z)),
                              ((nb051AlphaDummy012 x y A B C),
                                (nb051AlphaDummy014 x y z)),
                              ((nb051AlphaDummy037 x y A B C),
                                (nb051AlphaDummy038 x y z)),
                              ((nb051AlphaDummy035 x y A B C),
                                (nb051AlphaDummy036 x y z)),
                              ((nb051AlphaDummy004 x y A B C),
                                (nb051AlphaDummy006 x y z)),
                              ((nb051AlphaDummy003 x y A B C),
                                (nb051AlphaDummy005 x y z)),
                              ((nb051AlphaDummy033 x y A B C),
                                (nb051AlphaDummy034 x y z)),
                              ((nb051AlphaDummy007 x y A B C),
                                (nb051AlphaDummy008 x y z)),
                              ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                              ((nb051AlphaDummy001 x y A B C),
                                (nb051AlphaDummy002 x y z A B C))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part024`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb051_variable_occurrence`. -/
@[expose]
noncomputable def nb051VariableOccurrence (x y z : Var) (A B C : Class) :
    TAlphaClass
      [((nb051AlphaDummy004 x y A B C), (nb051AlphaDummy006 x y z)),
        ((nb051AlphaDummy003 x y A B C), (nb051AlphaDummy005 x y z)),
        ((nb051AlphaDummy033 x y A B C), (nb051AlphaDummy034 x y z)),
        ((nb051AlphaDummy007 x y A B C), (nb051AlphaDummy008 x y z)),
        ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      (Class.cv (nb051AlphaDummy000 x y A B C)) (Class.cv z) :=
  by
  have freshness0 :
    (nb051AlphaDummy000 x y A B C) ≠ (nb051AlphaDummy004 x y A B C) :=
    by
    unfold nb051AlphaDummy004
    with_reducible
      exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 1))
  have freshness1 : z ≠ (nb051AlphaDummy006 x y z) :=
    by
    unfold nb051AlphaDummy006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 1))
  have freshness2 :
    (nb051AlphaDummy000 x y A B C) ≠ (nb051AlphaDummy003 x y A B C) :=
    by
    unfold nb051AlphaDummy003
    with_reducible
      exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 0))
  have freshness3 : z ≠ (nb051AlphaDummy005 x y z) :=
    by
    unfold nb051AlphaDummy005
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 0))
  have freshness4 :
    (nb051AlphaDummy000 x y A B C) ≠ (nb051AlphaDummy033 x y A B C) :=
    by
    unfold nb051AlphaDummy033
    with_reducible
      exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0046 x y A B C) 0))
  have freshness5 : z ≠ (nb051AlphaDummy034 x y z) :=
    by
    unfold nb051AlphaDummy034
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0047 x y z) 0))
  have freshness6 :
    (nb051AlphaDummy000 x y A B C) ≠ (nb051AlphaDummy007 x y A B C) :=
    by
    unfold nb051AlphaDummy007
    with_reducible
      exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0043 x y A B C) 0))
  have freshness7 : z ≠ (nb051AlphaDummy008 x y z) :=
    by
    unfold nb051AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0045 x y z) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.here _ _ _))))))

/-- Checked nominal proof certificate identified upstream as `nb051_split_alpha_0004`. -/
@[expose]
noncomputable def nb051SplitAlpha0004 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      (Wff.classEq (Class.cv (nb051AlphaDummy001 x y A B C))
        (synCop (synCop (Class.cv x) (Class.cv y))
          (Class.cv (nb051AlphaDummy000 x y A B C))))
      (Wff.classEq (Class.cv (nb051AlphaDummy002 x y z A B C))
        (synCop (synCop (Class.cv x) (Class.cv y)) (Class.cv z))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0004 x y A B C) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0005 x y z A B C) 0)))
        (TAlphaVar.there
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0002 x y A B C) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0003 x y z A B C) 0)))
          (TAlphaVar.there (Ne.symm
              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0000 x y A B C) 0))) (Ne.symm
              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0001 x y z A B C) 0)))
            (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg
                          (nb051SplitAlpha0001 x y z A B C dv_x_z dv_y_z)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg
                          (nb051SplitAlpha0001 x y z A B C dv_x_z dv_y_z)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (nb051VariableOccurrence x y z A B C)) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((synCop (Class.cv x) (Class.cv y))).fv ∪
                                    ((Class.cv (nb051AlphaDummy000 x y A B C))).fv)
                                  (by decide)) (freshVar_injective
                                  (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb051SplitAlpha0003 x y z A B C))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb051AlphaDummy035 x y A B C),
        (nb051AlphaDummy036 x y z)), ((nb051AlphaDummy004 x y A B C),
        (nb051AlphaDummy006 x y z)), ((nb051AlphaDummy003 x y A B C),
        (nb051AlphaDummy005 x y z)), ((nb051AlphaDummy033 x y A B C),
        (nb051AlphaDummy034 x y z)), ((nb051AlphaDummy007 x y A B C),
        (nb051AlphaDummy008 x y z)), ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                                        ((nb051AlphaDummy001 x y A B C),
        (nb051AlphaDummy002 x y z A B C))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (nb051VariableOccurrence x y z A B C)) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((synCop (Class.cv x) (Class.cv y))).fv ∪
                                    ((Class.cv (nb051AlphaDummy000 x y A B C))).fv)
                                  (by decide)) (freshVar_injective
                                  (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb051SplitAlpha0003 x y z A B C))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb051AlphaDummy035 x y A B C),
        (nb051AlphaDummy036 x y z)), ((nb051AlphaDummy004 x y A B C),
        (nb051AlphaDummy006 x y z)), ((nb051AlphaDummy003 x y A B C),
        (nb051AlphaDummy005 x y z)), ((nb051AlphaDummy033 x y A B C),
        (nb051AlphaDummy034 x y z)), ((nb051AlphaDummy007 x y A B C),
        (nb051AlphaDummy008 x y z)), ((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                                        ((nb051AlphaDummy001 x y A B C),
        (nb051AlphaDummy002 x y z A B C))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part025`. -/


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

theorem nb051_focused_notmem_0000 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy000 x y A B C) ∉ A.fv :=
  by
  change
    freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))))

theorem nb051_focused_notmem_0001 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy000 x y A B C) ∉ B.fv :=
  by
  change
    freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb051_wpp_notmem_0110 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy000 x y A B C) ∉
      ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  by
  simpa only [nb051AlphaDummy000, fv_syn_wa, Finset.mem_union, fv_wff_classMem,
    fv_class_cv, Finset.mem_singleton, not_or] using
    (And.intro (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0018 x y A B C) 0)))
        (nb051_focused_notmem_0000 x y A B C)) (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0019 x y A B C) 0)))
        (nb051_focused_notmem_0001 x y A B C)))

theorem nb051_wpp_notmem_0111 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    z ∉ ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv := by
  simp only [fv_syn_wa, Finset.mem_union, fv_wff_classMem, fv_class_cv, (Ne.symm dv_x_z),
    Finset.mem_singleton, dv_A_z, (Ne.symm dv_y_z), dv_B_z, or_false, not_false_eq_true]

theorem nb051_focused_notmem_0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy001 x y A B C) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ({(nb051AlphaDummy000 x y A B C)} : Finset Var) ∪
          ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C)).symm ▸
            (Finset.mem_union_left _ (((fv_syn_wa (Wff.classMem (Class.cv x) A)
                    (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_left _
                  (((fv_wff_classMem (Class.cv x) A).symm ▸
                    (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_focused_notmem_0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy001 x y A B C) ∉ B.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ({(nb051AlphaDummy000 x y A B C)} : Finset Var) ∪
          ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C)).symm ▸
            (Finset.mem_union_left _ (((fv_syn_wa (Wff.classMem (Class.cv x) A)
                    (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_right _
                  (((fv_wff_classMem (Class.cv y) B).symm ▸
                    (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_wpp_notmem_0112 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy001 x y A B C) ∉
      ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  by
  simpa only [nb051AlphaDummy001, fv_syn_wa, Finset.mem_union, fv_wff_classMem,
    fv_class_cv, Finset.mem_singleton, not_or] using
    (And.intro (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0000 x y A B C) 0)))
        (nb051_focused_notmem_0002 x y A B C)) (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0002 x y A B C) 0)))
        (nb051_focused_notmem_0003 x y A B C)))

theorem nb051_focused_notmem_0004 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy002 x y z A B C) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv z) C))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv z) C)).symm ▸ (Finset.mem_union_left _
              (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)).symm ▸
                (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv x) A).symm ▸
                    (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_focused_notmem_0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy002 x y z A B C) ∉ B.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv z) C))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv z) C)).symm ▸ (Finset.mem_union_left _
              (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)).symm ▸
                (Finset.mem_union_right _ (((fv_wff_classMem (Class.cv y) B).symm ▸
                    (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_wpp_notmem_0113 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    (nb051AlphaDummy002 x y z A B C) ∉
      ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  by
  simpa only [nb051AlphaDummy002, fv_syn_wa, Finset.mem_union, fv_wff_classMem,
    fv_class_cv, Finset.mem_singleton, not_or] using
    (And.intro (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0001 x y z A B C) 0)))
        (nb051_focused_notmem_0004 x y z A B C)) (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0003 x y z A B C) 0)))
        (nb051_focused_notmem_0005 x y z A B C)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part026`. -/


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

theorem nb051_compact_envfresh_0008 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    TEnvFresh
      [((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb051AlphaDummy000 x y A B C) z (nb051_wpp_notmem_0110 x y A B C)
      (nb051_wpp_notmem_0111 x y z A B dv_A_z dv_B_z dv_x_z dv_y_z) (TEnvFresh.consSame y
        (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051AlphaDummy001 x y A B C)
            (nb051AlphaDummy002 x y z A B C) (nb051_wpp_notmem_0112 x y A B C)
            (nb051_wpp_notmem_0113 x y z A B C) (TEnvFresh.nil
              ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv)))))

/-- Checked nominal proof certificate identified upstream as `nb051_wpp_refl_0008`. -/
@[expose]
noncomputable def nb051WppRefl0008 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    TReflOn
      [((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      ((synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0008 x y z A B C dv_A_z dv_B_z dv_x_z dv_y_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part027`. -/


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

theorem nb051_focused_notmem_0006 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy000 x y A B C) ∉ C.fv :=
  by
  change
    freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0 ∉
      C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb051_wpp_notmem_0114 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy000 x y A B C) ∉ (C).fv := by
  simp only [(nb051_focused_notmem_0006 x y A B C), not_false_eq_true]

theorem nb051_wpp_notmem_0115 (z : Var) (C : Class) (dv_C_z : z ∉ C.fv) : z ∉ (C).fv := by
  simp only [dv_C_z, not_false_eq_true]

theorem nb051_focused_notmem_0007 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy001 x y A B C) ∉ C.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ({(nb051AlphaDummy000 x y A B C)} : Finset Var) ∪
          ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C))).fv)
        0 ∉
      C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C)).symm ▸
            (Finset.mem_union_right _
              (((fv_wff_classEq (Class.cv (nb051AlphaDummy000 x y A B C)) C).symm ▸
                (Finset.mem_union_right _ (hu))))))))

theorem nb051_wpp_notmem_0116 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051AlphaDummy001 x y A B C) ∉ (C).fv := by
  simp only [(nb051_focused_notmem_0007 x y A B C), not_false_eq_true]

theorem nb051_focused_notmem_0008 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy002 x y z A B C) ∉ C.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ((synWa (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv z) C))).fv)
        0 ∉
      C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv z) C)).symm ▸ (Finset.mem_union_right _
              (((fv_wff_classEq (Class.cv z) C).symm ▸ (Finset.mem_union_right _ (hu))))))))

theorem nb051_wpp_notmem_0117 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051AlphaDummy002 x y z A B C) ∉ (C).fv := by
  simp only [(nb051_focused_notmem_0008 x y z A B C), not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part028`. -/


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

theorem nb051_compact_envfresh_0009 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (dv_C_z : z ∉ C.fv) :
    TEnvFresh
      [((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      (C).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb051AlphaDummy000 x y A B C) z
      (nb051_wpp_notmem_0114 x y A B C) (nb051_wpp_notmem_0115 z C dv_C_z) (TEnvFresh.consSame y
        (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051AlphaDummy001 x y A B C)
            (nb051AlphaDummy002 x y z A B C) (nb051_wpp_notmem_0116 x y A B C)
            (nb051_wpp_notmem_0117 x y z A B C) (TEnvFresh.nil (C).fv)))))

/-- Checked nominal proof certificate identified upstream as `nb051_wpp_refl_0009`. -/
@[expose]
noncomputable def nb051WppRefl0009 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_C_z : z ∉ C.fv) :
    TReflOn
      [((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
        ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
      (C).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0009 x y z A B C dv_C_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part029`. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_mpt2`. -/
@[expose]
noncomputable def nominalDfMpt2 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_C_z : z ∉ C.fv)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCmpt2 x A y B C) (synCoprab x y z
          (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
            (.classEq (.cv z) C)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex
              (TAlphaWff.conj (nb051SplitAlpha0004 x y z A B C dv_x_z dv_y_z) (TAlphaWff.conj
                  (TAlphaWff.reflOfReflOn
                    [((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                      ((nb051AlphaDummy001 x y A B C), (nb051AlphaDummy002 x y z A B C))]
                    (synWa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                    (nb051WppRefl0008 x y z A B C dv_A_z dv_B_z dv_x_z dv_y_z))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.reflOfReflOn
                      [((nb051AlphaDummy000 x y A B C), z), (y, y), (x, x),
                        ((nb051AlphaDummy001 x y A B C),
                          (nb051AlphaDummy002 x y z A B C))]
                      C (nb051WppRefl0009 x y z A B C dv_C_z)))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
